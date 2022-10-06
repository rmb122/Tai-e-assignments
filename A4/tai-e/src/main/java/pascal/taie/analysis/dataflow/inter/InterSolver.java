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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;

import java.util.HashSet;
import java.util.List;
import java.util.Queue;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        Node entryPoint = this.icfg.getEntryOf(this.getMainMethod(this.icfg));
        this.result.setOutFact(entryPoint, this.analysis.newBoundaryFact(entryPoint));

        for (Node node : this.icfg) {
            if (node != entryPoint) {
                this.result.setInFact(node, this.analysis.newInitialFact());
                this.result.setOutFact(node, this.analysis.newInitialFact());
            }
        }
    }

    private Method getMainMethod(ICFG<Method, Node> icfg) {
        List<Method> methods = icfg.entryMethods().toList();
        if (methods.size() != 1) {
            throw new RuntimeException("Multiple entry point of icfg found");
        }
        return methods.get(0);
    }

    private void doSolve() {
        // TODO - finish me

        HashSet<Node> workList = new HashSet<>();
        Node entryPoint = this.icfg.getEntryOf(this.getMainMethod(this.icfg));

        for (Node node : icfg) {
            if (!node.equals(entryPoint)) {
                workList.add(node);
            }
        }

        while (!workList.isEmpty()) {
            Node current = workList.iterator().next();
            workList.remove(current);

            Fact inFact = result.getInFact(current);

            icfg.getInEdgesOf(current).forEach(inEdge -> {
                Node sourceNode = inEdge.getSource();
                Fact transferredOutFact = this.analysis.transferEdge(inEdge, this.result.getOutFact(sourceNode));
                this.analysis.meetInto(transferredOutFact, inFact);
            });

            Fact outFact = result.getOutFact(current);

            if (this.analysis.transferNode(current, inFact, outFact)) {
                workList.addAll(icfg.getSuccsOf(current));
            }
        }
    }
}
