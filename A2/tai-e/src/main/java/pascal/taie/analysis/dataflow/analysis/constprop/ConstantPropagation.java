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

import jas.CP;
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
import soot.util.Cons;

import java.util.Optional;

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
        CPFact res = new CPFact();
        cfg.getMethod().getIR().getParams().stream().forEach(param -> res.update(param, Value.getNAC()));

        // The default value is UNDEF.
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        // The default value is UNDEF.
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var v: fact.keySet()) {
            if (!ConstantPropagation.canHoldInt(v)) continue;
            target.update(v, this.meetValue(fact.get(v), target.get(v)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isConstant() && v2.isConstant()) {
            int valOfV1 = v1.getConstant();
            int valOfV2 = v2.getConstant();
            if (valOfV1 == valOfV2) {
                return Value.makeConstant(valOfV1);
            } else {
                return Value.getNAC();
            }
        } else if (v1.isConstant() && v2.isUndef() || v2.isConstant() && v1.isUndef()) {
            int val = v1.isConstant() ? v1.getConstant() : v2.getConstant();
            return Value.makeConstant(val);
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (!(stmt instanceof DefinitionStmt<?, ?>) || stmt.getDef().isEmpty()) {
            // Identity Function
            // if (in != null) {
            //     out.copyFrom(in);
            // }
            out.copyFrom(in);
            return false;
        }

        // Create temporary CPFact
        CPFact newOut = new CPFact();
        newOut.copyFrom(in);

        Var lhs = (Var) stmt.getDef().get();

        // Kill defined variable ifPresent
        newOut.remove(lhs);

        // Calculate the gen set
        for (RValue use : stmt.getUses()) {
            newOut.update(lhs, ConstantPropagation.evaluate(use, newOut));
        }

        if (newOut.equals(in)) {
            return false;
        } else {
            out.clear();
            out.copyFrom(newOut);
            return true;
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
     * Handle BinaryExp
     * @param lhs
     * @param rhs
     * @param exp
     * @param in
     * @return
     */
    public static Value handleBinary(Value lhs, Value rhs, BinaryExp exp, CPFact in) {
        if (lhs.isNAC() && !rhs.isNAC() || !lhs.isNAC() && rhs.isNAC()) {
            return Value.getNAC();
        } else if (lhs.isConstant() && rhs.isConstant()) {
            int v1 = lhs.getConstant();
            int v2 = rhs.getConstant();

            if (exp instanceof ArithmeticExp) {
                switch (((ArithmeticExp) exp).getOperator()) {
                    case ADD:
                        return Value.makeConstant(v1 + v2);
                    case SUB:
                        return Value.makeConstant(v1 - v2);
                    case MUL:
                        return Value.makeConstant(v1 * v2);
                    case DIV:
                        if (rhs.getConstant() == 0) {
                            return Value.getUndef();
                        } else {
                            return Value.makeConstant(v1 / v2);
                        }
                    case REM:
                        if (rhs.getConstant() == 0) {
                            return Value.getUndef();
                        } else {
                            return Value.makeConstant(v1 % v2);
                        }
                }
            } else if (exp instanceof ConditionExp) {
                return switch (((ConditionExp) exp).getOperator()) {
                    case EQ -> v1 == v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case GE -> v1 >= v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case GT -> v1 > v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case LE -> v1 <= v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case LT -> v1 < v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                    case NE -> v1 != v2 ? Value.makeConstant(1) : Value.makeConstant(0);
                };
            } else if (exp instanceof ShiftExp) {
                return switch (((ShiftExp) exp).getOperator()) {
                    case SHL -> Value.makeConstant(v1 << v2);
                    case SHR -> Value.makeConstant(v1 >> v2);
                    case USHR -> Value.makeConstant(v1 >>> v2);
                };
            } else if (exp instanceof BitwiseExp) {
                return switch (((BitwiseExp) exp).getOperator()) {
                    case OR -> Value.makeConstant(v1 | v2);
                    case AND -> Value.makeConstant(v1 & v2);
                    case XOR -> Value.makeConstant(v1 ^ v2);
                };
            }
        }

        return Value.getUndef();
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof BinaryExp) {
            Value lhs = in.get(((BinaryExp) exp).getOperand1());
            Value rhs = in.get(((BinaryExp) exp).getOperand2());
            return ConstantPropagation.handleBinary(lhs, rhs, (BinaryExp) exp, in);
        }

        return Value.getNAC();
    }
}
