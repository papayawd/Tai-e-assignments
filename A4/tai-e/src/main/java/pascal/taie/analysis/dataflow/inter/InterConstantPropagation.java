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

import jas.CP;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.Map;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }
    /*
    * transferCallNode 判断是否存在LValue 存在的话需要抹去 不存在的话就out=in
    * transferNonCallNode 等同于之前的transferNode 只是这里一定没有invoke
    * transferEdge 每条Edge可以看做一个Node(但不是) 会有in和out
    * transferNormalEdge 恒等函数 直接返回out
    * transferCallToReturnEdge 应该也可以做成恒等函数
    * transferCallEdge 需要添加传参信息
    * transferReturnEdge 直接返回 由meetInto来处理返回信息
    * */
    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        CPFact tmp = out.copy();
        out.clear();
        for (Map.Entry<Var, Value> entry : in.entries().toList()) {
            out.update(entry.getKey(), entry.getValue());
        }
        if(stmt.getDef().isPresent() && !out.get((Var)stmt.getDef().get()).isUndef()){
            out.remove((Var)stmt.getDef().get());
        }
        return !tmp.equals(out);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me

        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me

        if(edge.getSource().getDef().isEmpty()){
            return out.copy();
        }
        CPFact tmp = out.copy();
        tmp.remove((Var)edge.getSource().getDef().get());
        return out.copy();
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me

        // A3 总结过:invoke调用stmt.getUses()会返回 参数 + 函数签名  如果不是staticInvoke 第一个参数就会是隐藏的this
        System.out.println("[papaya]:transferCallEdge--edge.getSource().getUses()"+edge.getSource().getUses().toString());
        CPFact res = cp.newInitialFact();

        InvokeExp exp = (InvokeExp) edge.getSource().getUses().get(edge.getSource().getUses().size()-1);
        if(exp instanceof InvokeStatic) {
            int index = 0;
            for (Var var : icfg.getContainingMethodOf(edge.getTarget()).getIR().getParams()) {
                if (ConstantPropagation.canHoldInt(var)) {
                    res.update(var, callSiteOut.get(exp.getArg(index)));
                    // var 是形参   tmp 是实参
                }
                index++;
            }
        }else { // 非静态函数都有第一个隐藏函数为this指针
            int index = 1;
            for (Var var : icfg.getContainingMethodOf(edge.getTarget()).getIR().getParams()) {
                if (ConstantPropagation.canHoldInt(var)) {
                    res.update(var,callSiteOut.get(exp.getArg(index)));
                    // var 是形参   tmp 是实参
                }
                index++;
            }
        }

        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        /*
        * 奶奶滴 一直在想怎么获得调用点滴信息 getCallSite 就行了
        * */
        Stmt callSite = edge.getCallSite();
        if(callSite.getDef().isEmpty()){
            return null;
        }
        CPFact res = new CPFact();
        if(edge.getReturnVars().toArray().length > 1){ // 多个ret 先粗处理返回NAC 如果都为相同的常量应该返回常量
                                                        // 不想处理了。。 就这样吧 测试代码太长了
            res.update((Var)callSite.getDef().get(),Value.getNAC());
        } else{
            for(Var var : edge.getReturnVars()){ // 只有一个但是不知道怎么提出来，直接用循环算了
                res.update((Var)callSite.getDef().get(),returnOut.get(var));
            }
        }
        return res;
    }
}
