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
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import polyglot.ast.Call;

import java.security.PrivateKey;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    private Set<JMethod> RM = new HashSet<>(); // Reachable method

    private Collection<Stmt> S = new HashSet<>(); // Reachable stmts
    private StoreField field;

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
    private void addReachable(JMethod method) { // 不要忘记在该方法中处理静态字段 loads/stores 和静态方法调用。
        // TODO - finish me
        if (!RM.contains(method)) {
            RM.add(method);
            callGraph.addReachableMethod(method);
            S.addAll(method.getIR().getStmts());
            for (Stmt stmt : method.getIR().getStmts()) {
                if (stmt instanceof New) { // x = New T()
                    if (stmt.getDef().isEmpty()) continue;
                    // 不知道会不会出现x.f = New的情况 但是感觉生成的IR会用临时变量替换为 x = New的情况
                    Var var = ((New) stmt).getLValue();
                    PointsToSet new_pts = new PointsToSet();
                    new_pts.addObject(heapModel.getObj((New) stmt));
                    workList.addEntry(pointerFlowGraph.getVarPtr(var), new_pts);
                }else if (stmt instanceof Copy) { // x = y
                    Var x = ((Copy) stmt).getLValue();
                    Var y = ((Copy) stmt).getRValue();
                    addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getVarPtr(x));
                } else if(stmt instanceof StoreField && ((StoreField) stmt).isStatic()){ // 静态字段 T.f = y
                    addPFGEdge(pointerFlowGraph.getVarPtr(((StoreField) stmt).getRValue()),
                            pointerFlowGraph.getStaticField(((StoreField) stmt).getFieldRef().resolve()));
                } else if(stmt instanceof LoadField && ((LoadField) stmt).isStatic()){ // 静态字段 y = T.f
                    addPFGEdge(pointerFlowGraph.getStaticField(((LoadField) stmt).getFieldRef().resolve()),
                            pointerFlowGraph.getVarPtr(((LoadField) stmt).getLValue()));
                } else if(stmt instanceof Invoke && ((Invoke) stmt).isStatic()){ // 静态方法  x = T.m()
                    JMethod m = ((Invoke) stmt).getMethodRef().resolve();
                    addReachable(m); // 静态方法 addReachable
                    List<Var> ai = ((Invoke) stmt).getInvokeExp().getArgs(); // 实参
                    List<Var> mi = m.getIR().getParams(); // 形参
                    for(int i=0;i<ai.size();i++){
                        addPFGEdge(pointerFlowGraph.getVarPtr(ai.get(i)),
                                pointerFlowGraph.getVarPtr(mi.get(i)));
                    }
                    if (stmt.getDef().isPresent()) { // 如果是 r = invoke() 添加ret到r到边
                        Var r = ((Invoke) stmt).getLValue();
                        for (Var returnVar : m.getIR().getReturnVars()) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),
                                    pointerFlowGraph.getVarPtr(r));
                        }
                    }
                }
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> { // 不用他那个什么高级玩意 直接硬着头皮写
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) { // 没有 source -> target 这条边
            pointerFlowGraph.addEdge(source, target);
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() { // 不要忘记在这个方法中处理数组 loads/stores。
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet dt = propagate(ptr, pts);
            if (ptr instanceof VarPtr) {
                for (Obj obj : dt) {
                    for (StoreField storeField : ((VarPtr) ptr).getVar().getStoreFields()) { // x.f = y
                        JField jField = storeField.getFieldRef().resolve(); // 实例方法
                        Pointer target = pointerFlowGraph.getInstanceField(obj, jField);
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()), target);
                    }
                    for (LoadField loadField : ((VarPtr) ptr).getVar().getLoadFields()) { // y = x.f
                        System.out.println("[papaya]:loadField ----- "+loadField.toString());
                        JField jField = loadField.getFieldRef().resolve(); // 实例方法
                        Pointer source = pointerFlowGraph.getInstanceField(obj, jField);
                        addPFGEdge(source,pointerFlowGraph.getVarPtr(loadField.getLValue()));
                    }
                    for (StoreArray storeArray : ((VarPtr) ptr).getVar().getStoreArrays()) { // x[i] = y
                        Pointer target = pointerFlowGraph.getArrayIndex(obj); // 数组store oi[*]
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()), target);
                    }
                    for (LoadArray loadArray : ((VarPtr) ptr).getVar().getLoadArrays()) { // y = x[i]
                        Pointer source = pointerFlowGraph.getArrayIndex(obj); // 数组load  oi[*]
                        addPFGEdge(source, pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    }
                    processCall(((VarPtr) ptr).getVar(), obj);
                }
            } else if (ptr instanceof ArrayIndex) {
            } else if (ptr instanceof StaticField) {
            } else if (ptr instanceof InstanceField) {
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet ret = new PointsToSet();
        for (Obj object : pointsToSet.getObjects()) {
            if (!pointer.getPointsToSet().contains(object)) { // pts - pt(n)
                ret.addObject(object);
            }
        }
        if (!ret.isEmpty()) {
            for (Obj object : ret.getObjects()) {
                pointer.getPointsToSet().addObject(object); // pt(n) v= pts
            }
            for (Pointer target : pointerFlowGraph.getSuccsOf(pointer)) { //  pointer -> target
                workList.addEntry(target, ret); //
            }
        }

        return ret;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke : var.getInvokes()) { // 实例调用
            JMethod m = resolveCallee(recv, invoke); // 替代Dispatch
            if (m == null) continue;
            PointsToSet tmp_pts = new PointsToSet();
            tmp_pts.addObject(recv);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), tmp_pts);

            if (!callGraph.getCallersOf(m).contains(invoke)) { // 不存在 invoke -> m    不知道用法对没有
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m));
                addReachable(m); // 实例方法 addReachable
                List<Var> pi = m.getIR().getParams();
                List<Var> ai = invoke.getInvokeExp().getArgs();
                for (int i = 0; i < pi.size(); i++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(ai.get(i)),
                            pointerFlowGraph.getVarPtr(pi.get(i)));
                }
                if (invoke.getDef().isPresent()) { // 如果是 r = invoke() 添加ret到r到边
                    Var r = invoke.getLValue();
                    for (Var returnVar : m.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),
                                pointerFlowGraph.getVarPtr(r));
                    }
                }
            }
        }
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
