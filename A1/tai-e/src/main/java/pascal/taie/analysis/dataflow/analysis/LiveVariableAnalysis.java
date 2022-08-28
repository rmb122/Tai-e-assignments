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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.Optional;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        return new SetFact<>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        return new SetFact<>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
        target.union(fact);
    }

    private void removeIfContains(SetFact<Var> setFact, Var var) {
        if (setFact.contains(var)) {
            setFact.remove(var);
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me

        SetFact<Var> inCopy = in.copy();
        in.set(out);

        Optional<LValue> lValueOptional = stmt.getDef();

        if (lValueOptional.isPresent()) {
            LValue lValue = lValueOptional.get();
            if (lValue instanceof ArrayAccess) {
                removeIfContains(in, ((ArrayAccess) lValue).getBase());
                removeIfContains(in, ((ArrayAccess) lValue).getIndex());
            } else if (lValue instanceof Var) {
                removeIfContains(in, (Var) lValue);
            } else if (lValue instanceof InstanceFieldAccess) {
                removeIfContains(in, ((InstanceFieldAccess) lValue).getBase());
            }
        }

        stmt.getUses().forEach(use -> {
            if (use instanceof Var) {
                in.add((Var) use);
            }
        });

        return !inCopy.equals(in);
    }
}
