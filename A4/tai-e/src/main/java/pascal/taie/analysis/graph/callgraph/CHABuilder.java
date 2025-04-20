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

import java.lang.invoke.CallSite;
import java.util.*;

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

        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod current = workList.poll();
            if (callGraph.contains(current)) continue;
            callGraph.addReachableMethod(current);  // add reachable and add all call sites for this JMethod

            for (Invoke invoke : callGraph.getCallSitesIn(current)) {
                Set<JMethod> res = resolve(invoke);
                if (res == null) continue;
                for (JMethod target : res) {
                    // TODO: CallKInd.OTHER 得改一下吧？
                    callGraph.addEdge(new Edge<>(CallKind.OTHER, invoke, target));
                    workList.add(target);
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> res = new HashSet<>();
        JClass declaringClassType = callSite.getMethodRef().getDeclaringClass();
        Subsignature subSignature = callSite.getMethodRef().getSubsignature();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC:
                res.add(dispatch(declaringClassType, subSignature));
                break;
            case OTHER:
            case DYNAMIC:
            case SPECIAL:
                JMethod dispatchedJMethod = dispatch(declaringClassType, subSignature);
                if (dispatchedJMethod != null) {
                    res.add(dispatchedJMethod);
                }
                break;
            case INTERFACE:
                System.out.println("Interface");
            case VIRTUAL:
                Queue<JClass> subclasses = new LinkedList<>();
                subclasses.add(declaringClassType);
                while (!subclasses.isEmpty()) {
                    JClass current = subclasses.poll();
                    JMethod temp = dispatch(current, subSignature);
                    if (temp != null) {
                        res.add(temp);
                    }
                    subclasses.addAll(this.hierarchy.getDirectSubclassesOf(current));
                    subclasses.addAll(this.hierarchy.getDirectImplementorsOf(current));
                }
        }

        if (!res.isEmpty()) {
            return res;
        } else {
            return null;
        }
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        for (JMethod method : jclass.getDeclaredMethods()) {
            if (!method.isAbstract() && method.getSubsignature().equals(subsignature)) {
                return method;
            }
        }

        if (jclass.getSuperClass() != null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        }


        return null;
    }
}
