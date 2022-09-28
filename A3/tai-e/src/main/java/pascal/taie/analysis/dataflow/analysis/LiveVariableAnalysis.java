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




package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Binary;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me

        return new SetFact<Var>();
        // return new SetFact<>(cfg.getExit().getUses().stream().map(x->(Var)x).toList());
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        return new SetFact<Var>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me

        // 按照文档说的合并
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me

        // backward 方式
        // 创建out临时变量 方便做前后对比
        SetFact<Var> tmp = in.copy();

        in.union(out);
        // in = out.copy();

        // 减去def
        in.removeIf(var -> stmt.getDef().isPresent() && var == stmt.getDef().get()); //

        // 合并 use
        for (RValue rValue : stmt.getUses()) { // 遍历
            process(rValue, in);
        }
        // return tmp != in;    // wrong  一直返回true 停不下来
        return !tmp.equals(in);
    }

    private void process(RValue value, SetFact<Var> in) {
        if (value instanceof Var) {
            in.add((Var) value);
        } else if (value instanceof InvokeInstanceExp) {    // 函数调用
            processInvokeInstanceExp((InvokeInstanceExp) value, in);
        } else if (value instanceof BinaryExp) {            // 二元运算 获取每个Operand
            process(((BinaryExp) value).getOperand1(), in);
            process(((BinaryExp) value).getOperand1(), in);
        } else if (value instanceof ArrayLengthExp) {       // The .length property of an array
            in.add(((ArrayLengthExp) value).getBase());     // a.length()   a就是use元素
            // in.add(((ArrayLengthExp) value).getOperand());
        } else if (value instanceof ArrayAccess) {          // 数组访问  a[1] 或者 a[b] 所以参数可能是use元素
            in.add(((ArrayAccess) value).getBase());
            in.add(((ArrayAccess) value).getIndex());
        } else {                                            // 输出没有被处理的类型
            System.out.println(value.getClass().toString());
        }


    }

    private void processInvokeInstanceExp(InvokeInstanceExp exp, SetFact<Var> in) {
        // 函数调用 一般是class.function(a1,a2,...)
        in.add(exp.getBase());                              // class名是use
        for (RValue value : exp.getUses()) {                // 参数也是uses
            process(value, in);
        }
    }
}