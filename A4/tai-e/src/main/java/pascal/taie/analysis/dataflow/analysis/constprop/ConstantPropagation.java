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

package pascal.taie.analysis.dataflow.analysis.constprop;

import heros.solver.Pair;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Map;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me


        CPFact cpFact = new CPFact();
        // 参数全为NAC
        for (Var var : cfg.getIR().getParams()) {
            //System.out.println("[*]param: "+var.toString());
            if (canHoldInt(var)) {
                cpFact.update(var, Value.getNAC());
            }
        }

        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me

        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        // undef 不会出现在map中
        for (Map.Entry<Var, Value> entry : fact.entries().toList()) {
            if (target.get(entry.getKey()).isUndef()) {    // (NAC,undef) or (v,undef) = NAC or v
                target.update(entry.getKey(), entry.getValue());
            } else {                                       // 都不是undef
                target.update(entry.getKey(), meetValue(entry.getValue(), target.get(entry.getKey())));
            }
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {        // v1 v2 都不是undef
        // TODO - finish me

        if (v1.isNAC() || v2.isNAC()) {                   // 其中有NAC 结果就是NAC
            return Value.getNAC();
        } else {                                           // v1 v2 都是常数
            if (v1.getConstant() != v2.getConstant()) {   // v1 != v2 返回NAC
                return Value.getNAC();
            } else {
                return v1;                              // v1 == v2 返回任意一个
            }
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        CPFact tmp = out.copy();
        // out = in
        out.clear();
        for (Map.Entry<Var, Value> entry : in.entries().toList()) {
            out.update(entry.getKey(), entry.getValue());
        }
        System.out.println("[papaya]:stmt----"+stmt.toString());
        if (!(stmt instanceof DefinitionStmt)) return !tmp.equals(out);         // 判断是否赋值语句
        if (stmt.getDef().isEmpty() || !(stmt.getDef().get() instanceof Var)) return !tmp.equals(out);
        if (!canHoldInt((Var) stmt.getDef().get())) return !tmp.equals(out);    // 判断是否是int类型

        // 暂时没有考虑 右边有浮点数的情况
        Var x = (Var) stmt.getDef().get();
        Pair<Var, Value> pair_x = new Pair<Var, Value>(x, out.get(x));
        boolean flag = false;

        if (!out.get(x).equals(Value.getUndef())) {  // 删除原本的x  先删掉x就需要提前记录
            out.remove(x);
            flag = true;
        }
        // x = y + z  实用stmt.getUses() 返回 [y, z, y + z] 和预期不一样 不能遍历
        // 如果是函数调用 stmt.getUses() 会返回 this + 参数 + 函数签名    size = 1 + count(param) + 1
        // 比如 x = y + f(z, w)  stmt.getUses() 返回 [y, this, z, w, sig]
        if (stmt.getUses().size() == 3 // 只处理 x = y op z
                && !stmt.getUses().get(2).toString().contains("invoke")) {
            process(pair_x, flag, x, stmt.getUses().get(2), out); // 只取最后一个  也就是 BinaryExp
            // 需要考虑 x = x + 1 情况
        } else if(stmt.getUses().size() == 1) { // 只处理 x = y
            process(pair_x, flag, x, stmt.getUses().get(0), out); // 此外就是 x = y的情况
        }
        else{ // 剩下的肯定是invoke调用 这里处理为NAC
            out.update(x,Value.getNAC());
        }
//        for (RValue rValue : stmt.getUses()) { // 不能采用遍历
//            process(pair_x,flag, x, rValue, out); // 需要考虑 x = NAC && x = x + 1 情况
//        }


//        System.out.println("[papaya]:" + stmt.getUses().size());
        if(stmt.getUses().size() >= 2){
            System.out.println("[papaya]:" + stmt.getUses());
        }
//        System.out.println("[papaya]:" + stmt.getDef().toString() + " = " + stmt.getUses());
//        System.out.println("[papaya]:" + out.toString());
        return !tmp.equals(out);

    }

    void process(Pair<Var, Value> pair_x, boolean flag, Var key, RValue rvalue, CPFact out) {
        if (rvalue instanceof Var) {                        // x = y 变量
            if (out.get((Var) rvalue).equals(Value.getUndef())) return; // y is undef 不处理
            out.update(key, out.get((Var) rvalue));
        } else if (rvalue instanceof IntLiteral) {          // x = 1 常量
            out.update(key, Value.makeConstant(((IntLiteral) rvalue).getValue()));
        } else if (rvalue instanceof BinaryExp) {           // x = y + z 二元运算
            if (flag && // 被删除过 并且 是 x = x op y的情况 需要将x加回来
                    (((BinaryExp) rvalue).getOperand1().equals(pair_x.getO1())
                            || ((BinaryExp) rvalue).getOperand2().equals(pair_x.getO1()))) {
                out.update(pair_x.getO1(),pair_x.getO2());
            }

            if (!canHoldInt(((BinaryExp) rvalue).getOperand1()) // 考虑等式右边有 非Int 但是感觉不会出现这种复杂情况
                    || !canHoldInt(((BinaryExp) rvalue).getOperand2())) {

                return; // 不处理 但是要还原删除的东西
            }
            if (out.get(((BinaryExp) rvalue).getOperand1()).equals(Value.getUndef()) // 考虑等式右边有undef
                    || out.get(((BinaryExp) rvalue).getOperand2()).equals(Value.getUndef())) {

                return; // 不处理
            }
            //System.out.println("[papaya]:"+rvalue.toString());
            out.update(key, evaluate((BinaryExp) rvalue, out));
            // x = NAC && x = x + 1 情况考虑
        } else if (rvalue instanceof InvokeVirtual) {
            out.update(key, Value.getNAC());
        } else {                                            // 输出没有被处理的类型
            out.update(key, Value.getNAC());
            //System.out.println("[papaya]" + rvalue.getClass().toString());
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param out IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(BinaryExp exp, CPFact out) {
        // TODO - finish me

        // v1 v2 会存在 undef !!!
        Value v1 = out.get(exp.getOperand1());
        Value v2 = out.get(exp.getOperand2());
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }


        if (exp instanceof ArithmeticExp) {                         // + - * / %
            switch (exp.getOperator().toString()) {
                case "+":
                    //System.out.println("[papaya]:" + exp.toString());
                    return Value.makeConstant(v1.getConstant() + v2.getConstant());
                case "-":
                    return Value.makeConstant(v1.getConstant() - v2.getConstant());
                case "*":
//                    for (Map.Entry<Var, Value> entry : out.entries().toList()) {
//                        System.out.println(entry.getKey().toString()+"----------"+entry.getValue().toString());
//                    }
                    return Value.makeConstant(v1.getConstant() * v2.getConstant());
                case "/":
                    if (v2.getConstant() == 0) return Value.getNAC();   //   y / 0 = NAC
                    else return Value.makeConstant(v1.getConstant() / v2.getConstant());
                case "%":
                    return Value.makeConstant(v1.getConstant() % v2.getConstant());
                default:
                    return Value.getNAC();
            }

        } else if (exp instanceof ConditionExp) {                   // 比较运算
            return switch (exp.getOperator().toString()) {
                case "==" -> Value.makeConstant(v1.getConstant() == v2.getConstant() ? 1 : 0);
                case "!=" -> Value.makeConstant(v1.getConstant() != v2.getConstant() ? 1 : 0);
                case "<" -> Value.makeConstant(v1.getConstant() < v2.getConstant() ? 1 : 0);
                case ">" -> Value.makeConstant(v1.getConstant() > v2.getConstant() ? 1 : 0);
                case "<=" -> Value.makeConstant(v1.getConstant() <= v2.getConstant() ? 1 : 0);
                case ">=" -> Value.makeConstant(v1.getConstant() >= v2.getConstant() ? 1 : 0);
                default -> Value.getNAC();
            };

        } else if (exp instanceof ShiftExp) {                       // 位运算
            return switch (exp.getOperator().toString()) {
                case "<<" -> Value.makeConstant(v1.getConstant() << v2.getConstant());
                case ">>" -> Value.makeConstant(v1.getConstant() >> v2.getConstant());
                case ">>>" -> Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                default -> Value.getNAC();
            };

        } else if (exp instanceof BitwiseExp) { // and or xor
            return switch (exp.getOperator().toString()) {
                case "|" -> Value.makeConstant(v1.getConstant() | v2.getConstant());
                case "&" -> Value.makeConstant(v1.getConstant() & v2.getConstant());
                case "^" -> Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                default -> Value.getNAC();
            };
        } else return Value.getNAC();
    }
}
