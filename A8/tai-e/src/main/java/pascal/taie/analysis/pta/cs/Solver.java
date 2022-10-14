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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me

        if (!this.callGraph.contains(csMethod)) {
            this.callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().stmts().forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            // x = new T()
            Obj obj = Solver.this.heapModel.getObj(stmt);
            Context objContext = Solver.this.contextSelector.selectHeapContext(this.csMethod, obj);
            PointsToSet pointsToSet = PointsToSetFactory.make(Solver.this.csManager.getCSObj(objContext, obj));
            Pointer pointer = Solver.this.csManager.getCSVar(this.context, stmt.getLValue());
            Solver.this.workList.addEntry(pointer, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y
            Pointer dst = Solver.this.csManager.getCSVar(this.context, stmt.getLValue());
            Pointer src = Solver.this.csManager.getCSVar(this.context, stmt.getRValue());
            Solver.this.addPFGEdge(src, dst);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // x = Static.field
            if (stmt.getRValue() instanceof StaticFieldAccess) {
                Pointer dst = Solver.this.csManager.getCSVar(this.context, stmt.getLValue());
                Pointer src = Solver.this.csManager.getStaticField(stmt.getRValue().getFieldRef().resolve());
                Solver.this.addPFGEdge(src, dst);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // Static.field = x
            if (stmt.getLValue() instanceof StaticFieldAccess) {
                Pointer dst = Solver.this.csManager.getStaticField(stmt.getLValue().getFieldRef().resolve());
                Pointer src = Solver.this.csManager.getCSVar(this.context, stmt.getRValue());
                Solver.this.addPFGEdge(src, dst);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // x = Static.method(y, z)
            if (stmt.isStatic()) {
                CSCallSite csCallSite = Solver.this.csManager.getCSCallSite(this.context, stmt);
                JMethod method = Solver.this.resolveCallee(null, stmt);
                Context calleeContext = Solver.this.contextSelector.selectContext(csCallSite, method);
                Solver.this.processCallEdge(csCallSite, Solver.this.csManager.getCSMethod(calleeContext, method));
                Solver.this.taintAnalysis.processTaintInvoke(null, null, csCallSite, method);
                Solver.this.taintAnalysis.collectSinkCallSite(stmt, method);
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

            if (delta.size() > 0 && entry.pointer() instanceof CSVar csVar) {
                delta.forEach(obj -> {
                    Var var = csVar.getVar();
                    Context context = csVar.getContext();

                    // x.field = y
                    var.getStoreFields().forEach(storeField -> {
                        this.addPFGEdge(this.csManager.getCSVar(context, storeField.getRValue()), this.csManager.getInstanceField(obj, storeField.getFieldAccess().getFieldRef().resolve()));
                    });

                    // x = y.field
                    var.getLoadFields().forEach(loadField -> {
                        this.addPFGEdge(this.csManager.getInstanceField(obj, loadField.getFieldAccess().getFieldRef().resolve()), this.csManager.getCSVar(context, loadField.getLValue()));
                    });

                    // x[y] = z
                    var.getStoreArrays().forEach(storeArray -> {
                        this.addPFGEdge(this.csManager.getCSVar(context, storeArray.getRValue()), this.csManager.getArrayIndex(obj));
                    });

                    // x = y[z]
                    var.getLoadArrays().forEach(loadArray -> {
                        this.addPFGEdge(this.csManager.getArrayIndex(obj), this.csManager.getCSVar(context, loadArray.getLValue()));
                    });

                    this.processCall(csVar, obj);
                    this.processArg(csVar);
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
        PointsToSet delta = PointsToSetFactory.make();
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

    public void workListAddEntry(Pointer pointer, PointsToSet pointsToSet) {
        this.workList.addEntry(pointer, pointsToSet);
    }

    private void processCallEdge(CSCallSite csCallSite, CSMethod csMethod) {
        if (!this.callGraph.getCalleesOf(csCallSite).contains(csMethod)) {
            Context callerContext = csCallSite.getContext();
            Context calleeContext = csMethod.getContext();

            this.addReachable(csMethod);
            this.callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(csCallSite.getCallSite()), csCallSite, csMethod));

            List<Var> actualArgs = csCallSite.getCallSite().getInvokeExp().getArgs();
            List<Var> formalArgs = csMethod.getMethod().getIR().getParams();

            for (int i = 0; i < actualArgs.size(); i++) {
                this.addPFGEdge(this.csManager.getCSVar(callerContext, actualArgs.get(i)), this.csManager.getCSVar(calleeContext, formalArgs.get(i)));
            }

            if (csCallSite.getCallSite().getLValue() != null) {
                List<Var> returnVars = csMethod.getMethod().getIR().getReturnVars();
                returnVars.forEach(returnVar -> {
                    this.addPFGEdge(this.csManager.getCSVar(calleeContext, returnVar), this.csManager.getCSVar(callerContext, csCallSite.getCallSite().getLValue()));
                });
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me

        Context callerContext = recv.getContext();

        recv.getVar().getInvokes().forEach(invoke -> {
            JMethod method = this.resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = this.csManager.getCSCallSite(callerContext, invoke);
            Context calleeContext = this.contextSelector.selectContext(csCallSite, recvObj, method);
            this.workList.addEntry(this.csManager.getCSVar(calleeContext, method.getIR().getThis()), PointsToSetFactory.make(recvObj));

            CSMethod csMethod = this.csManager.getCSMethod(calleeContext, method);
            this.processCallEdge(csCallSite, csMethod);

            this.taintAnalysis.processTaintInvoke(recv, recvObj, csCallSite, method);
            this.taintAnalysis.collectSinkCallSite(invoke, method);
        });
    }

    private void processArg(CSVar csVar) {
        // 存在拿 taint object 作参数的情况, 重新计算 taint

        Context callerContext = csVar.getContext();

        csVar.getVar().getMethod().getIR().stmts().forEach(stmt -> {
            if (stmt instanceof Invoke invoke) {
                if (invoke.getRValue().getArgs().contains(csVar.getVar())) {
                    CSCallSite csCallSite = this.csManager.getCSCallSite(callerContext, invoke);
                    if (invoke.isStatic()) {
                        this.taintAnalysis.processTaintInvoke(null, null, csCallSite, this.resolveCallee(null, invoke));
                    } else if (invoke.getInvokeExp() instanceof InvokeInstanceExp invokeInstanceExp) {
                        Var base = invokeInstanceExp.getBase();
                        CSVar csBase = this.csManager.getCSVar(callerContext, base);

                        csBase.getPointsToSet().getObjects().forEach(obj -> {
                            JMethod method = this.resolveCallee(obj, invoke);
                            this.taintAnalysis.processTaintInvoke(csBase, obj, csCallSite, method);
                        });
                    }
                }
            }
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
