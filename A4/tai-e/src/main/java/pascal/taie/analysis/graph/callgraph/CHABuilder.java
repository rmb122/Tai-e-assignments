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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.HashSet;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me

        HashSet<JMethod> workList = new HashSet<>();
        workList.add(entry);

        while (!workList.isEmpty()) {
            JMethod current = workList.iterator().next();
            workList.remove(current);

            if (callGraph.contains(current)) {
                continue;
            } else {
                callGraph.addReachableMethod(current);
            }

            callGraph.callSitesIn(current).forEach(invokeStmt -> {
                Set<JMethod> targetMethods = this.resolve(invokeStmt);

                targetMethods.forEach(method -> {
                    CallKind kind = CallGraphs.getCallKind(invokeStmt);
                    callGraph.addEdge(new Edge<>(kind, invokeStmt, method));
                });

                workList.addAll(targetMethods);
            });
        }
        return callGraph;
    }

    private Set<JClass> getSubClasses(JClass jClass) {
        Set<JClass> jClasses = new HashSet<>();

        if (jClass.isInterface()) {
            this.hierarchy.getDirectSubinterfacesOf(jClass).forEach(subClass -> {
                jClasses.addAll(getSubClasses(subClass));
            });
            this.hierarchy.getDirectImplementorsOf(jClass).forEach(subClass -> {
                jClasses.addAll(getSubClasses(subClass));
            });
        } else {
            jClasses.add(jClass);
            this.hierarchy.getDirectSubclassesOf(jClass).forEach(subClass -> {
                jClasses.addAll(getSubClasses(subClass));
            });
        }
        return jClasses;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> methods = new HashSet<>();

        MethodRef methodRef = callSite.getMethodRef();
        JClass clazz = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();

        if (callSite.isStatic()) {
            methods.add(clazz.getDeclaredMethod(subsignature));
        } else if (callSite.isSpecial()) {
            methods.add(this.dispatch(clazz, subsignature));
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            Set<JClass> subClasses = this.getSubClasses(clazz);
            subClasses.forEach(subClass -> {
                JMethod method = this.dispatch(subClass, subsignature);
                if (method != null) {
                    methods.add(method);
                }
            });
        }
        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me

        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (jMethod != null && !jMethod.isAbstract()) {
            return jMethod;
        } else {
            jclass = jclass.getSuperClass();
            if (jclass == null) {
                return null;
            } else {
                return dispatch(jclass, subsignature);
            }
        }
    }
}
