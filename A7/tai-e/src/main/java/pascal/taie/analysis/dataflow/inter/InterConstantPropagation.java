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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private MultiMap<Var, Var> alias;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        this.alias = this.initializeAlias(pta);
    }

    private MultiMap<Var, Var> initializeAlias(PointerAnalysisResult pta) {
        MultiMap<Var, Var> alias = Maps.newMultiMap();
        MultiMap<Obj, Var> objToVars = Maps.newMultiMap();

        pta.getVars().forEach(var -> {
            pta.getPointsToSet(var).forEach(obj -> {
                objToVars.put(obj, var);
            });
        });

        objToVars.forEachSet(((obj, vars) -> {
            vars.forEach(var -> {
                // 包含自己
                alias.putAll(var, vars);
            });
        }));
        return alias;
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt.getDef().isPresent()) {
            LValue lValue = stmt.getDef().get();
            if (lValue instanceof Var var && ConstantPropagation.canHoldInt((Var) lValue)) {
                if (stmt instanceof LoadField loadFieldStmt) {
                    CPFact oldOutFact = out.copy();
                    in.forEach(out::update);

                    Set<StoreField> storeStmts = null;

                    if (loadFieldStmt.isStatic()) {
                        storeStmts = this.getStaticFieldStoreStmt(this.solver.getICFG(), loadFieldStmt.getFieldAccess().getFieldRef());
                    } else {
                        if (loadFieldStmt.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                            storeStmts = this.getVarStoreStmt(this.alias.get(instanceFieldAccess.getBase()), loadFieldStmt.getFieldAccess().getFieldRef());
                        } else {
                            throw new RuntimeException("Unexpected non-instanceFieldAccess found");
                        }
                    }

                    Value inValue = in.get(var);
                    out.update(var, this.cp.meetValue(inValue, this.mergeStoreStmtValue(storeStmts)));
                    return !oldOutFact.equals(out);
                } else if (stmt instanceof LoadArray loadArrayStmt) {
                    CPFact oldOutFact = out.copy();
                    in.forEach(out::update);

                    Set<Var> baseAlias = this.alias.get(loadArrayStmt.getArrayAccess().getBase());
                    Set<StoreArray> storeArrays = this.getArrayStoreStmt(baseAlias);

                    Var indexVar = loadArrayStmt.getArrayAccess().getIndex();
                    Value indexValue = this.solver.getNodeInFact(loadArrayStmt).get(indexVar);

                    Value inValue = in.get(var);
                    out.update(var, this.cp.meetValue(inValue, this.mergeArrayStoreStmtValue(storeArrays, indexValue)));
                    return !oldOutFact.equals(out);
                } else {
                    return this.cp.transferNode(stmt, in, out);
                }
            } else if (stmt instanceof StoreField storeFieldStmt && ConstantPropagation.canHoldInt(storeFieldStmt.getRValue())) {
                // store 通知 load 更新, 加入 worklist
                Set<LoadField> stmts = null;
                if (storeFieldStmt.isStatic()) {
                    stmts = this.getStaticFieldLoadStmt(this.solver.getICFG(), storeFieldStmt.getFieldAccess().getFieldRef());
                } else {
                    if (storeFieldStmt.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                        stmts = this.getVarLoadStmt(this.alias.get(instanceFieldAccess.getBase()), storeFieldStmt.getFieldAccess().getFieldRef());
                    } else {
                        throw new RuntimeException("Unexpected non-instanceFieldAccess found");
                    }
                }
                this.solver.getWorkList().addAll(stmts);
                // use default out.copyFrom(in);
            } else if (stmt instanceof StoreArray storeArrayStmt && ConstantPropagation.canHoldInt(storeArrayStmt.getRValue())) {
                Var base = storeArrayStmt.getArrayAccess().getBase();
                Set<Var> baseAlias = this.alias.get(base);
                this.solver.getWorkList().addAll(this.getVarArrayLoad(baseAlias));
                // use default out.copyFrom(in);
            }
        }
        return out.copyFrom(in);
    }

    private Set<StoreField> getStaticFieldStoreStmt(ICFG<JMethod, Stmt> icfg, FieldRef fieldRef) {
        Set<StoreField> result = new HashSet<>();
        for (Stmt stmt : icfg) {
            if (stmt instanceof StoreField storeField && storeField.getFieldAccess().getFieldRef().equals(fieldRef)) {
                result.add(storeField);
            }
        }
        return result;
    }

    private Set<LoadField> getStaticFieldLoadStmt(ICFG<JMethod, Stmt> icfg, FieldRef fieldRef) {
        Set<LoadField> result = new HashSet<>();
        for (Stmt stmt : icfg) {
            if (stmt instanceof LoadField loadField && loadField.getFieldAccess().getFieldRef().equals(fieldRef)) {
                result.add(loadField);
            }
        }
        return result;
    }

    private Set<StoreField> getVarStoreStmt(Set<Var> vars, FieldRef fieldRef) {
        Set<StoreField> result = new HashSet<>();

        vars.forEach(var -> {
            List<StoreField> storeFields = var.getStoreFields();
            storeFields.forEach(storeField -> {
                if (storeField.getFieldAccess().getFieldRef().equals(fieldRef)) {
                    result.add(storeField);
                }
            });
        });

        return result;
    }

    private Set<LoadField> getVarLoadStmt(Set<Var> vars, FieldRef fieldRef) {
        Set<LoadField> result = new HashSet<>();

        vars.forEach(var -> {
            List<LoadField> loadFields = var.getLoadFields();
            loadFields.forEach(loadField -> {
                if (loadField.getFieldAccess().getFieldRef().equals(fieldRef)) {
                    result.add(loadField);
                }
            });
        });

        return result;
    }

    private Value mergeStoreStmtValue(Set<StoreField> storeFields) {
        Value value = Value.getUndef();

        for (StoreField storeField : storeFields) {
            value = this.cp.meetValue(value, this.solver.getNodeInFact(storeField).get(storeField.getRValue()));
        }

        return value;
    }

    private Set<StoreArray> getArrayStoreStmt(Set<Var> vars) {
        Set<StoreArray> result = new HashSet<>();

        vars.forEach(var -> {
            result.addAll(var.getStoreArrays());
        });

        return result;
    }

    private Value mergeArrayStoreStmtValue(Set<StoreArray> storeArrays, Value indexValue) {
        Value value = Value.getUndef();

        for (StoreArray storeArray : storeArrays) {
            Var storeRValue = storeArray.getRValue();
            Var storeIndex = storeArray.getArrayAccess().getIndex();
            Value storeIndexValue = this.solver.getNodeInFact(storeArray).get(storeIndex);

            // alias 的四种情况
            if (indexValue.isConstant() && storeIndexValue.isConstant() && indexValue.getConstant() == storeIndexValue.getConstant()
                    || indexValue.isNAC() && storeIndexValue.isNAC()
                    || indexValue.isConstant() && storeIndexValue.isNAC()
                    || indexValue.isNAC() && storeIndexValue.isConstant()) {
                // merge 是 alias 的 value
                value = this.cp.meetValue(value, this.solver.getNodeInFact(storeArray).get(storeRValue));
            }
        }

        return value;
    }

    private Set<LoadArray> getVarArrayLoad(Set<Var> vars) {
        Set<LoadArray> result = new HashSet<>();
        vars.forEach(var -> {
            result.addAll(var.getLoadArrays());
        });
        return result;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt source = edge.getSource();
        CPFact result = out.copy();

        if (source instanceof Invoke invokeStmt) {
            Var defVar = invokeStmt.getResult();
            if (defVar != null) {
                // kill def
                result.update(defVar, Value.getUndef());
            }
        } else {
            throw new RuntimeException("source not a Invoke");
        }

        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Stmt source = edge.getSource();
        CPFact result = new CPFact();

        if (source instanceof Invoke invokeStmt) {
            List<Var> vars = invokeStmt.getRValue().getArgs();
            List<Var> calleeVars = edge.getCallee().getIR().getParams();
            for (int i = 0; i < vars.size(); i++) {
                result.update(calleeVars.get(i), callSiteOut.get(vars.get(i)));
            }
        } else {
            throw new RuntimeException("callSite not a Invoke");
        }

        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        Stmt callSite = edge.getCallSite();
        CPFact result = new CPFact();

        if (callSite instanceof Invoke invokeStmt) {
            Var defVar = invokeStmt.getResult();

            if (defVar != null) {
                Value returnValue = Value.getUndef();

                for (Var returnVar : edge.getReturnVars()) {
                    returnValue = cp.meetValue(returnValue, returnOut.get(returnVar));
                }

                result.update(defVar, returnValue);
            }
        } else {
            throw new RuntimeException("callSite not a Invoke");
        }

        return result;
    }
}
