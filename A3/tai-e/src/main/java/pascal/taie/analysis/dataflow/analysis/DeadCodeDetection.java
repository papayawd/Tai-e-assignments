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

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        List<Stmt> LabeledList = new ArrayList<Stmt>();
        Queue<Stmt> WorkList = new LinkedList<Stmt>();
        WorkList.add(cfg.getEntry());
        LabeledList.add(cfg.getEntry());
        while (!WorkList.isEmpty()) {
            Stmt stmt = WorkList.poll();

            // 先考虑死代码  分支不可达
            if (stmt instanceof If) {
                ConditionExp exp = ((If) stmt).getCondition();
                Value v1 = constants.getInFact(stmt).get(exp.getOperand1());
                Value v2 = constants.getInFact(stmt).get(exp.getOperand2());
                if (v1.isNAC() || v2.isNAC() || v1.isUndef() || v2.isUndef()) {
                    // 计算结果不是常量 两条边都要遍历
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (!LabeledList.contains(edge.getTarget())) { // 没有遍历过的才去遍历 不然死循环
                            LabeledList.add(edge.getTarget());
                            WorkList.add((edge.getTarget()));
                        }
                    }
                    continue;
                }

                int res = switch (exp.getOperator().toString()) {
                    case "==" -> v1.getConstant() == v2.getConstant() ? 1 : 0;
                    case "!=" -> v1.getConstant() != v2.getConstant() ? 1 : 0;
                    case "<" -> v1.getConstant() < v2.getConstant() ? 1 : 0;
                    case ">" -> v1.getConstant() > v2.getConstant() ? 1 : 0;
                    case "<=" -> v1.getConstant() <= v2.getConstant() ? 1 : 0;
                    case ">=" -> v1.getConstant() >= v2.getConstant() ? 1 : 0;
                    default -> 0;
                };
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    if ((res == 1 && edge.getKind() == Edge.Kind.IF_TRUE) // 只进入true
                            || (res == 0 && edge.getKind() == Edge.Kind.IF_FALSE)) { // 只进入false
                        if (!LabeledList.contains(edge.getTarget())) { // 没有遍历过的才去遍历 不然死循环
                            LabeledList.add(edge.getTarget());
                            WorkList.add((edge.getTarget()));
                        }
                    }
                }
            } else if (stmt instanceof SwitchStmt) {
                Value res = constants.getInFact(stmt).get(((SwitchStmt) stmt).getVar());
                if (res.isNAC() || res.isUndef()) { // 所有case + default都应该遍历
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (!LabeledList.contains(edge.getTarget())) { // 没有遍历过的才去遍历 不然死循环
                            LabeledList.add(edge.getTarget());
                            WorkList.add((edge.getTarget()));
                        }
                    }
                    continue;
                }
                boolean flag = true;
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    if (edge.getKind() == Edge.Kind.SWITCH_CASE
                            && edge.getCaseValue() == res.getConstant()) { // 找到匹配的case 进入
                        flag = false; // 不进入 default
                        if (!LabeledList.contains(edge.getTarget())) { // 没有遍历过的才去遍历 不然死循环
                            LabeledList.add(edge.getTarget());
                            WorkList.add((edge.getTarget()));
                        }
                    }
                }
                if (flag) { // 需要进入 default
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT) { // 找到default 进入
                            if (!LabeledList.contains(edge.getTarget())) { // 没有遍历过的才去遍历 不然死循环
                                LabeledList.add(edge.getTarget());
                                WorkList.add((edge.getTarget()));
                            }
                        }
                    }
                }
            } else { // 不是跳转语句 直接进入唯一的下一条语句
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    if (!LabeledList.contains(edge.getTarget())) {
                        LabeledList.add(edge.getTarget());
                        WorkList.add((edge.getTarget()));
                    }
                }
            }

            // 再考虑无效赋值
            if (stmt instanceof AssignStmt) { // 赋值语句
                LValue lvalue = stmt.getDef().isPresent() ? (stmt).getDef().get() : null;
                if (lvalue instanceof Var) { // 左边是Var   应该所有情况都是吧。。。
                    if (!liveVars.getOutFact(stmt).contains((Var)lvalue)){ // 该变量没有存活
                        deadCode.add(stmt);
                    }
                }
            }
        }

        for(Stmt stmt:cfg.getNodes()){ // 没有标记的都是死代码
            if(stmt.getLineNumber() >=0 && !LabeledList.contains(stmt)){ // 莫名其妙出现Line -1
                deadCode.add(stmt);
            }
        }
//        for(Stmt stmt:cfg.getNodes()){
//            System.out.println(String.format("[papaya]: [%d@L%d] %s",stmt.getIndex(),stmt.getLineNumber(),stmt.toString()));
//        }
        /*
         * 首先是死代码 分为控制流不可达和分支不可达
         *   控制流不可达就从entry开始遍历cfg 无条件进入任何分支 没有被遍历的就是控制流不可达到
         *   分支不可达也是从需要常量传播，如果条件是常量并且不满足 那么就不应该进入改分支 没有被遍历的就是控制流不可达到
         *   这样的话分支不可达 一定包含 控制流不可达
         *
         * 然后是无效赋值 需要活跃变量信息 如果赋值语句的左边(LValue)是非活跃变量 那么就是无效赋值
         *
         * */
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
