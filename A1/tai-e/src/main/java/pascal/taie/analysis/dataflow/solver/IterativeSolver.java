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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Set;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me

        LinkedList<Node> queue = new LinkedList<>();
        Node exit = cfg.getExit();

        // 如果采用 BFS 等算法, 从 exit 节点出发, 碰到 while(true) 死循环, 会导致寻找不到可用的前驱
        // 所以还是用 work list 吧

        for (Node i : cfg) {
            if (!i.equals(exit)) {
                queue.add(i);
            }
        }

        while (queue.size() != 0) {
            Node currStmt = queue.poll();

            Set<Node> succs = cfg.getSuccsOf(currStmt);
            Fact outFact = result.getOutFact(currStmt);
            for (Node i : succs) {
                this.analysis.meetInto(result.getInFact(i), outFact);
            }

            boolean changed = this.analysis.transferNode(currStmt, result.getInFact(currStmt), outFact);
            if (changed) {
                queue.addAll(cfg.getPredsOf(currStmt));
            }
        }
    }
}
