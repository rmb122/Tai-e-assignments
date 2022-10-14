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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import javax.annotation.Nullable;
import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final HashMap<JMethod, Source> sourceMethod;
    private final HashMap<JMethod, TaintTransfer> baseToResultTransfer;
    private final HashMap<JMethod, HashMap<Integer, TaintTransfer>> argToResultTransfer;
    private final HashMap<JMethod, HashMap<Integer, TaintTransfer>> argToBaseTransfer;

    private final HashMap<JMethod, HashMap<Integer, Sink>> sinkMethod;

    private final Set<CallSitePair> sinkCallSites;

    private static class CallSitePair {
        Invoke callSite;
        JMethod method;

        CallSitePair(Invoke callSite, JMethod method) {
            this.callSite = callSite;
            this.method = method;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            CallSitePair that = (CallSitePair) o;
            return Objects.equals(callSite, that.callSite) && Objects.equals(method, that.method);
        }

        @Override
        public int hashCode() {
            return Objects.hash(callSite, method);
        }
    }

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);

        this.sourceMethod = new HashMap<>();
        this.baseToResultTransfer = new HashMap<>();
        this.argToResultTransfer = new HashMap<>();
        this.argToBaseTransfer = new HashMap<>();
        this.sinkMethod = new HashMap<>();
        this.sinkCallSites = new HashSet<>();

        this.config.getSources().forEach(source -> {
            this.sourceMethod.put(source.method(), source);
        });

        this.config.getTransfers().forEach(taintTransfer -> {
            if (taintTransfer.from() == TaintTransfer.BASE && taintTransfer.to() == TaintTransfer.RESULT) {
                this.baseToResultTransfer.put(taintTransfer.method(), taintTransfer);
            } else if (taintTransfer.from() >= 0 && taintTransfer.to() == TaintTransfer.RESULT) {
                JMethod method = taintTransfer.method();
                if (!argToResultTransfer.containsKey(method)) {
                    argToResultTransfer.put(method, new HashMap<>());
                }
                argToResultTransfer.get(method).put(taintTransfer.from(), taintTransfer);
            } else if (taintTransfer.from() >= 0 && taintTransfer.to() == TaintTransfer.BASE) {
                JMethod method = taintTransfer.method();
                if (!argToBaseTransfer.containsKey(method)) {
                    argToBaseTransfer.put(method, new HashMap<>());
                }
                argToBaseTransfer.get(method).put(taintTransfer.from(), taintTransfer);
            }
        });

        this.config.getSinks().forEach(sink -> {
            JMethod method = sink.method();
            if (!sinkMethod.containsKey(method)) {
                sinkMethod.put(method, new HashMap<>());
            }
            this.sinkMethod.get(method).put(sink.index(), sink);
        });
    }

    // TODO - finish me
    private boolean isSourceMethod(JMethod method) {
        return this.sourceMethod.containsKey(method);
    }

    private boolean isBaseToResultTransferMethod(JMethod method) {
        return this.baseToResultTransfer.containsKey(method);
    }

    private boolean isArgToResultTransferMethod(JMethod method, Integer taintArgLocation) {
        return this.argToResultTransfer.containsKey(method) && this.argToResultTransfer.get(method).containsKey(taintArgLocation);
    }

    private boolean isArgToBaseTransferMethod(JMethod method, Integer taintArgLocation) {
        return this.argToBaseTransfer.containsKey(method) && this.argToBaseTransfer.get(method).containsKey(taintArgLocation);
    }

    private Obj getSourceTaintObject(Invoke callSite, JMethod method) {
        return this.manager.makeTaint(callSite, this.sourceMethod.get(method).type());
    }

    private Obj getBaseToResultTransferTaintObject(Invoke callSite, JMethod method) {
        return this.manager.makeTaint(callSite, this.baseToResultTransfer.get(method).type());
    }

    private Obj getArgToResultTransferObject(Invoke callSite, JMethod method, Integer taintArgLocation) {
        return this.manager.makeTaint(callSite, this.argToResultTransfer.get(method).get(taintArgLocation).type());
    }

    private Obj getArgToBaseTransferObject(Invoke callSite, JMethod method, Integer taintArgLocation) {
        return this.manager.makeTaint(callSite, this.argToBaseTransfer.get(method).get(taintArgLocation).type());
    }

    public void processTaintInvoke(@Nullable CSVar recv, @Nullable CSObj recvObj, CSCallSite csCallSite, JMethod calleeMethod) {
        Context callerContext = csCallSite.getContext();

        Var defVar = csCallSite.getCallSite().getLValue();
        if (defVar != null) {
            CSVar csDefVar = this.csManager.getCSVar(callerContext, defVar);
            Obj taintObject = null;

            // x = y.z(), result 存在的情况下
            // source 产生污点对象
            if (this.isSourceMethod(calleeMethod)) {
                taintObject = this.getSourceTaintObject(csCallSite.getCallSite(), calleeMethod);
            } else if (recv != null && recvObj != null && this.manager.isTaint(recvObj.getObject()) && this.isBaseToResultTransferMethod(calleeMethod)) {
                // 非静态方法
                // base -> result 传播对象
                taintObject = this.getBaseToResultTransferTaintObject(this.manager.getSourceCall(recvObj.getObject()), calleeMethod);
            } else {
                // arg -> result
                List<Var> args = csCallSite.getCallSite().getRValue().getArgs();

                for (int i = 0; i < args.size(); i++) {
                    PointsToSet pointsToSet = this.solver.getCSManager().getCSVar(callerContext, args.get(i)).getPointsToSet();
                    if (this.isArgToResultTransferMethod(calleeMethod, i)) {
                        Optional<CSObj> taintObj = pointsToSet.getObjects().stream().filter(obj -> this.manager.isTaint(obj.getObject())).findAny();
                        if (taintObj.isPresent()) {
                            taintObject = this.getArgToResultTransferObject(this.manager.getSourceCall(taintObj.get().getObject()), calleeMethod, i);
                            break;
                        }
                    }
                }
            }

            if (taintObject != null) {
                // Context context = this.csManager.getCSObj(this.solver.getContextSelector().selectHeapContext(csMethod, taintObject);
                CSObj csObj = this.csManager.getCSObj(this.emptyContext, taintObject);
                this.solver.workListAddEntry(csDefVar, PointsToSetFactory.make(csObj));
            }
        }

        if (recv != null && recvObj != null) {
            // arg -> base
            List<Var> args = csCallSite.getCallSite().getRValue().getArgs();

            for (int i = 0; i < args.size(); i++) {
                PointsToSet pointsToSet = this.solver.getCSManager().getCSVar(callerContext, args.get(i)).getPointsToSet();
                if (this.isArgToBaseTransferMethod(calleeMethod, i)) {
                    Optional<CSObj> taintObj = pointsToSet.getObjects().stream().filter(obj -> this.manager.isTaint(obj.getObject())).findAny();
                    if (taintObj.isPresent()) {
                        Obj taintObject = this.getArgToBaseTransferObject(this.manager.getSourceCall(taintObj.get().getObject()), calleeMethod, i);
                        this.solver.workListAddEntry(recv, PointsToSetFactory.make(this.csManager.getCSObj(this.emptyContext, taintObject)));
                        break;
                    }
                }
            }
        }
    }

    public void collectSinkCallSite(Invoke callSite, JMethod method) {
        if (this.sinkMethod.containsKey(method)) {
            this.sinkCallSites.add(new CallSitePair(callSite, method));
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        this.sinkCallSites.forEach(callSitePair -> {
            List<Var> args = callSitePair.callSite.getRValue().getArgs();
            for (int taintArgLocation = 0; taintArgLocation < args.size(); taintArgLocation++) {
                Set<Obj> pointsToSet = result.getPointsToSet(args.get(taintArgLocation));
                for (Obj obj : pointsToSet) {
                    if (this.manager.isTaint(obj)) {
                        boolean isSink = this.sinkMethod.get(callSitePair.method).containsKey(taintArgLocation);
                        if (isSink) {
                            taintFlows.add(new TaintFlow(this.manager.getSourceCall(obj), callSitePair.callSite, taintArgLocation));
                        }
                    }
                }
            }
        });

        return taintFlows;
    }
}
