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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me

        if (!this.callGraph.contains(method)) {
            this.callGraph.addReachableMethod(method);
            method.getIR().stmts().forEach(stmt -> stmt.accept(this.stmtProcessor));
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        StmtProcessor() {
        }

        @Override
        public Void visit(New stmt) {
            // x = new T()
            Obj obj = Solver.this.heapModel.getObj(stmt);
            PointsToSet pointsToSet = new PointsToSet(obj);
            Pointer pointer = Solver.this.pointerFlowGraph.getVarPtr(stmt.getLValue());
            Solver.this.workList.addEntry(pointer, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y
            Pointer dst = Solver.this.pointerFlowGraph.getVarPtr(stmt.getLValue());
            Pointer src = Solver.this.pointerFlowGraph.getVarPtr(stmt.getRValue());
            Solver.this.addPFGEdge(src, dst);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // x = Static.field
            if (stmt.getRValue() instanceof StaticFieldAccess) {
                Pointer dst = Solver.this.pointerFlowGraph.getVarPtr(stmt.getLValue());
                Pointer src = Solver.this.pointerFlowGraph.getStaticField(stmt.getRValue().getFieldRef().resolve());
                Solver.this.addPFGEdge(src, dst);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // Static.field = x
            if (stmt.getLValue() instanceof StaticFieldAccess) {
                Pointer dst = Solver.this.pointerFlowGraph.getStaticField(stmt.getLValue().getFieldRef().resolve());
                Pointer src = Solver.this.pointerFlowGraph.getVarPtr(stmt.getRValue());
                Solver.this.addPFGEdge(src, dst);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // x = Static.method(y, z)
            if (stmt.isStatic()) {
                JMethod method = Solver.this.resolveCallee(null, stmt);
                Solver.this.processCallEdge(stmt, method);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me

        if (!this.pointerFlowGraph.getSuccsOf(source).contains(target)) {
            this.pointerFlowGraph.addEdge(source, target);

            PointsToSet pointsToSet = source.getPointsToSet();
            if (!pointsToSet.isEmpty()) {
                this.workList.addEntry(target, pointsToSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = this.propagate(entry.pointer(), entry.pointsToSet());

            if (delta.size() > 0 && entry.pointer() instanceof VarPtr varPtr) {
                delta.forEach(obj -> {
                    // x.field = y
                    varPtr.getVar().getStoreFields().forEach(storeField -> {
                        this.addPFGEdge(this.pointerFlowGraph.getVarPtr(storeField.getRValue()), this.pointerFlowGraph.getInstanceField(obj, storeField.getFieldAccess().getFieldRef().resolve()));
                    });

                    // x = y.field
                    varPtr.getVar().getLoadFields().forEach(loadField -> {
                        this.addPFGEdge(this.pointerFlowGraph.getInstanceField(obj, loadField.getFieldAccess().getFieldRef().resolve()), this.pointerFlowGraph.getVarPtr(loadField.getLValue()));
                    });

                    // x[y] = z
                    varPtr.getVar().getStoreArrays().forEach(storeArray -> {
                        this.addPFGEdge(this.pointerFlowGraph.getVarPtr(storeArray.getRValue()), this.pointerFlowGraph.getArrayIndex(obj));
                    });

                    // x = y[z]
                    varPtr.getVar().getLoadArrays().forEach(loadArray -> {
                        this.addPFGEdge(this.pointerFlowGraph.getArrayIndex(obj), this.pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    });

                    this.processCall(varPtr.getVar(), obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        pointsToSet.forEach(obj -> {
            if (!pointer.getPointsToSet().contains(obj)) {
                pointer.getPointsToSet().addObject(obj);
                delta.addObject(obj);
            }
        });

        if (delta.size() > 0) {
            this.pointerFlowGraph.getSuccsOf(pointer).forEach(succsPointer -> {
                this.workList.addEntry(succsPointer, delta);
            });
        }
        return delta;
    }

    private void processCallEdge(Invoke invoke, JMethod method) {
        if (!this.callGraph.getCalleesOf(invoke).contains(method)) {
            this.addReachable(method);
            this.callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method));

            List<Var> actualArgs = invoke.getInvokeExp().getArgs();
            List<Var> formalArgs = method.getIR().getParams();

            for (int i = 0; i < actualArgs.size(); i++) {
                this.addPFGEdge(this.pointerFlowGraph.getVarPtr(actualArgs.get(i)), this.pointerFlowGraph.getVarPtr(formalArgs.get(i)));
            }

            if (invoke.getLValue() != null) {
                List<Var> returnVars = method.getIR().getReturnVars();
                returnVars.forEach(returnVar -> {
                    this.addPFGEdge(this.pointerFlowGraph.getVarPtr(returnVar), this.pointerFlowGraph.getVarPtr(invoke.getLValue()));
                });
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me

        var.getInvokes().forEach(invoke -> {
            JMethod method = this.resolveCallee(recv, invoke);
            this.workList.addEntry(this.pointerFlowGraph.getVarPtr(method.getIR().getThis()), new PointsToSet(recv));
            this.processCallEdge(invoke, method);
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
