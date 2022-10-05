/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact cpFact = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        params.forEach(x -> {
            if (ConstantPropagation.canHoldInt(x)) {
                cpFact.update(x, Value.getNAC());
            }
        });
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        target.forEach((k, v) -> {
            fact.update(k, this.meetValue(fact.get(k), v));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return v1;
            } else {
                return Value.getNAC();
            }
        }

        if (v1.isConstant() && v2.isUndef()) {
            return v1;
        }

        if (v2.isConstant() && v1.isUndef()) {
            return v2;
        }

        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        }

        throw new RuntimeException(String.format("Unexpected value of %s and %s", v1, v2));
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact oldFact = out.copy();

        in.forEach(out::update);

        stmt.getDef().ifPresent(lValue -> {
            if (lValue instanceof Var && ConstantPropagation.canHoldInt((Var) lValue)) {
                stmt.getUses().forEach(rValue -> {
                    if (rValue instanceof BinaryExp) {
                        Var left = ((BinaryExp) rValue).getOperand1();
                        Var right = ((BinaryExp) rValue).getOperand2();

                        if (ConstantPropagation.canHoldInt(left) && ConstantPropagation.canHoldInt(right)) {
                            if (rValue instanceof ArithmeticExp || rValue instanceof ConditionExp || rValue instanceof ShiftExp || rValue instanceof BitwiseExp) {
                                out.update((Var) lValue, ConstantPropagation.evaluate(rValue, in));
                            }
                        }
                    } else if (rValue instanceof Var) {
                        if (ConstantPropagation.canHoldInt((Var) rValue)) {
                            // is int type
                            Var rValueVar = (Var) rValue;
                            if (rValueVar.isTempConst()) {
                                out.update((Var) lValue, Value.makeConstant(((IntLiteral) rValueVar.getTempConstValue()).getValue()));
                            } else {
                                out.update((Var) lValue, in.get(rValueVar));
                            }
                        }
                    } else if (rValue instanceof IntLiteral) {
                        out.update((Var) lValue, Value.makeConstant(((IntLiteral) rValue).getValue()));
                    } else {
                        out.update((Var) lValue, Value.getNAC());
                    }
                });
            }
        });

        // 不等于 -> 需要重新计算
        return !oldFact.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    public static int booleanToInt(boolean bool) {
        if (bool) {
            return 1;
        } else {
            return 0;
        }
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me

        if (exp instanceof BinaryExp) {
            Var left = ((BinaryExp) exp).getOperand1();
            Var right = ((BinaryExp) exp).getOperand2();

            if ((left.isTempConst() || in.get(left).isConstant()) && (right.isTempConst() || in.get(right).isConstant())) {
                Integer leftLiteral = null;
                Integer rightLiteral = null;

                if (left.isTempConst()) {
                    leftLiteral = ((IntLiteral) left.getTempConstValue()).getValue();
                } else {
                    leftLiteral = in.get(left).getConstant();
                }

                if (right.isTempConst()) {
                    rightLiteral = ((IntLiteral) right.getTempConstValue()).getValue();
                } else {
                    rightLiteral = in.get(right).getConstant();
                }
                BinaryExp.Op op = ((BinaryExp) exp).getOperator();
                if (op.equals(ArithmeticExp.Op.ADD)) {
                    return Value.makeConstant(leftLiteral + rightLiteral);
                } else if (op.equals(ArithmeticExp.Op.SUB)) {
                    return Value.makeConstant(leftLiteral - rightLiteral);
                } else if (op.equals(ArithmeticExp.Op.MUL)) {
                    return Value.makeConstant(leftLiteral * rightLiteral);
                } else if (op.equals(ArithmeticExp.Op.DIV)) {
                    if (rightLiteral == 0) {
                        return Value.getUndef();
                    } else {
                        return Value.makeConstant(leftLiteral / rightLiteral);
                    }
                } else if (op.equals(ArithmeticExp.Op.REM)) {
                    if (rightLiteral == 0) {
                        return Value.getUndef();
                    } else {
                        return Value.makeConstant(leftLiteral % rightLiteral);
                    }
                } else if (op.equals(ShiftExp.Op.SHL)) {
                    return Value.makeConstant(leftLiteral << rightLiteral);
                } else if (op.equals(ShiftExp.Op.SHR)) {
                    return Value.makeConstant(leftLiteral >> rightLiteral);
                } else if (op.equals(ShiftExp.Op.USHR)) {
                    return Value.makeConstant(leftLiteral >>> rightLiteral);
                } else if (op.equals(BitwiseExp.Op.OR)) {
                    return Value.makeConstant(leftLiteral | rightLiteral);
                } else if (op.equals(BitwiseExp.Op.AND)) {
                    return Value.makeConstant(leftLiteral & rightLiteral);
                } else if (op.equals(BitwiseExp.Op.XOR)) {
                    return Value.makeConstant(leftLiteral ^ rightLiteral);
                } else if (op.equals(ConditionExp.Op.EQ)) {
                    return Value.makeConstant(booleanToInt(leftLiteral.equals(rightLiteral)));
                } else if (op.equals(ConditionExp.Op.NE)) {
                    return Value.makeConstant(booleanToInt(!leftLiteral.equals(rightLiteral)));
                } else if (op.equals(ConditionExp.Op.GE)) {
                    return Value.makeConstant(booleanToInt(leftLiteral >= rightLiteral));
                } else if (op.equals(ConditionExp.Op.GT)) {
                    return Value.makeConstant(booleanToInt(leftLiteral > rightLiteral));
                } else if (op.equals(ConditionExp.Op.LE)) {
                    return Value.makeConstant(booleanToInt(leftLiteral <= rightLiteral));
                } else if (op.equals(ConditionExp.Op.LT)) {
                    return Value.makeConstant(booleanToInt(leftLiteral < rightLiteral));
                }
            }

            if (in.get(left).isNAC() || in.get(right).isNAC()) {
                if (right.isTempConst() || in.get(right).isConstant()) {
                    Integer rightLiteral = null;

                    if (right.isTempConst()) {
                        rightLiteral = ((IntLiteral) right.getTempConstValue()).getValue();
                    } else {
                        rightLiteral = in.get(right).getConstant();
                    }
                    if (rightLiteral.equals(0) && (((BinaryExp) exp).getOperator().equals(ArithmeticExp.Op.REM) || ((BinaryExp) exp).getOperator().equals(ArithmeticExp.Op.DIV))) {
                        return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }

            return Value.getUndef();
        }
        throw new RuntimeException(exp + "is a expression that can't evaluate");
    }
}
