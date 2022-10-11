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
        // TODO - finish me

        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        LinkedList<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        Set<JMethod> RM = new HashSet<>(); // Reachable method
        while(!workList.isEmpty()){
            JMethod m = workList.poll();
            if(!RM.contains(m)){
                RM.add(m);
                System.out.println("[papaya]:[RM]"+m.toString());
                callGraph.addReachableMethod(m); // 标记method reachable
                for(Invoke callSite : callGraph.callSitesIn(m).toList()){
                    System.out.println("[papaya]:[callSite]"+callSite.toString());
                    Set<JMethod> T = resolve(callSite);
                    if(T.isEmpty()) continue;
                    for(JMethod mm : T){
                        System.out.println("[papaya]:[mm]"+mm.toString());
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite),callSite,mm));
                        workList.add(mm);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me

        Set<JMethod> T = new HashSet<>();
        JMethod m = callSite.getContainer();
        System.out.println("[papaya]:"+"[method]"+m.toString()+"[callSite]"+callSite.toString());
        CallKind callkind = CallGraphs.getCallKind(callSite);
        System.out.println("[papaya]:"+callkind.toString());
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        if (callkind.equals(CallKind.STATIC)) { // 注意这里添加的method获取路径有点绕 按道理来说Static和Special可以合并
            T.add(callSite.getMethodRef().getDeclaringClass().getDeclaredMethod(subsignature));
        } else if (callkind.equals(CallKind.SPECIAL)) {
            JMethod tmp = dispatch(callSite.getMethodRef().getDeclaringClass(),subsignature);
            if(tmp != null) T.add(tmp);
        }else if(callkind.equals(CallKind.VIRTUAL)){
            JClass c = callSite.getMethodRef().getDeclaringClass();
            JMethod tmp = dispatch(c,subsignature);
            if(tmp != null) T.add(tmp);
            for(JClass cc : hierarchy.getDirectSubclassesOf(c)){ // VIRTUAL 用这个 getDirectSubclassesOf
                System.out.println("[papaya]:"+"[getDirectSubclassesOf]"+cc.toString());
                JMethod _tmp = dispatch(cc,subsignature);
                if(_tmp != null) T.add(_tmp);
            }
        }
        else if(callkind.equals(CallKind.INTERFACE)){   // INTERFACE 用 getDirectImplementorsOf
                                                        // 不知道 getDirectSubinterfacesOf 有啥用
            JClass c = callSite.getMethodRef().getDeclaringClass();
            JMethod tmp = dispatch(c,subsignature);
            if(tmp != null) T.add(tmp);
            for(JClass cc : hierarchy.getDirectImplementorsOf(c)){
                System.out.println("[papaya]:"+"[getDirectImplementorsOf]"+cc.toString());
                JMethod _tmp = dispatch(cc,subsignature);
                if(_tmp != null) T.add(_tmp);
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        System.out.println("[papaya]:"+"[class]"+jclass.toString()+"[sign]"+subsignature.toString());
        for (JMethod jmethod : jclass.getDeclaredMethods()) {
            if (!jmethod.isAbstract() && jmethod.getSubsignature().equals(subsignature)) {
                System.out.println("[papaya]:find method");
                return jmethod;
            }
        }
        return jclass.getSuperClass() != null ? dispatch(jclass.getSuperClass(), subsignature) : null;
    }
}
