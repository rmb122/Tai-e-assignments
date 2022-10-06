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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
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
        return this.cp.transferNode(stmt, in, out);
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
