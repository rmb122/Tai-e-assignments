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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    private Set<Stmt> visitCFG(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        HashSet<Stmt> visitedStmt = new HashSet<>();
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());

        while (!queue.isEmpty()) {
            Stmt current = queue.poll();
            // BFS
            if (visitedStmt.contains(current)) {
                continue;
            } else {
                visitedStmt.add(current);
            }

            if (current instanceof If) {
                Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(current);
                ConditionExp conditionExp = ((If) current).getCondition();

                if (ConstantPropagation.canHoldInt(conditionExp.getOperand1()) && ConstantPropagation.canHoldInt(conditionExp.getOperand2())) {
                    Value result = ConstantPropagation.evaluate(conditionExp, constants.getInFact(current));

                    if (result.isConstant()) {
                        // 能够判断的 if
                        boolean conditionResult = result.getConstant() == 1;
                        outEdges.forEach(edge -> {
                            if (edge.getKind() == Edge.Kind.IF_TRUE && conditionResult) {
                                queue.add(edge.getTarget());
                            } else if (edge.getKind() == Edge.Kind.IF_FALSE && !conditionResult) {
                                queue.add(edge.getTarget());
                            }
                        });
                        // 能够判断, 直接 continue
                        continue;
                    }
                }
            }

            if (current instanceof SwitchStmt) {
                SwitchStmt switchStmt = (SwitchStmt) current;
                Var switchVar = switchStmt.getVar();
                if (ConstantPropagation.canHoldInt(switchVar) && constants.getInFact(switchStmt).get(switchVar).isConstant()) {
                    // var 为 int 可以判断, 这个判断应该是多余的
                    int switchVarValue = constants.getInFact(switchStmt).get(switchVar).getConstant();
                    Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(current);
                    Edge<Stmt> defaultEdge = null;
                    boolean foundTarget = false;

                    for (Edge<Stmt> edge : outEdges) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE) {
                            if (edge.getCaseValue() == switchVarValue) {
                                queue.add(edge.getTarget());
                                foundTarget = true;
                                break;
                            }
                        } else if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            defaultEdge = edge;
                        }
                    }

                    if (!foundTarget && defaultEdge != null) {
                        // 没有找到目标且存在 default, 使用 default, 其他情况直接 continue
                        queue.add(defaultEdge.getTarget());
                    }
                    continue;
                }
            }
            // 不是能够判断的 stmt, 直接添加后继
            queue.addAll(cfg.getSuccsOf(current));
        }

        return visitedStmt;
    }

    private Set<Stmt> getDeadAssignment(CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        HashSet<Stmt> deadAssignment = new HashSet<>();

        for (Stmt stmt : cfg) {
            stmt.getDef().ifPresent(lValue -> {
                if (lValue instanceof Var) {
                    if (!liveVars.getOutFact(stmt).contains((Var) lValue)) {
                        boolean noSideEffect = true;
                        for (RValue rValue : stmt.getUses()) {
                            noSideEffect &= DeadCodeDetection.hasNoSideEffect(rValue);
                        }
                        if (noSideEffect) {
                            deadAssignment.add(stmt);
                        }
                    }
                }
            });
        }

        return deadAssignment;
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        deadCode.addAll(cfg.getNodes());
        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());
        // entry 和 exit 是例外

        Set<Stmt> visitedStmt = this.visitCFG(cfg, constants);
        deadCode.removeAll(visitedStmt);
        deadCode.addAll(getDeadAssignment(cfg, liveVars));

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
