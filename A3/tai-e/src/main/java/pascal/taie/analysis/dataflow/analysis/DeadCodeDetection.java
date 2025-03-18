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
import pascal.taie.ir.stmt.*;

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

        // Let's find the dead assignments first
        for (Stmt stmt : cfg.getNodes()) {
            if (!(stmt instanceof AssignStmt<?, ?>)) continue;
            stmt.getDef().ifPresent(v -> {
                boolean hasNoSideEffect = true;
                for (RValue use : stmt.getUses()) {
                    hasNoSideEffect &= DeadCodeDetection.hasNoSideEffect(use);
                }
                if (hasNoSideEffect && (!liveVars.getOutFact(stmt).contains((Var) v))) {
                    deadCode.add(stmt);
                }
            });
        }

        // Let's find unreachable code then
        for (Stmt stmt : cfg.getNodes()) {
            if (stmt instanceof If) {
                handleIf(stmt, constants, cfg, deadCode);
            } else if (stmt instanceof SwitchStmt) {
                handleSwitch(stmt, constants, cfg, deadCode);
            }
        }

        // Finally, let's traverse the CFG and mark unvisited nodes as dead
        Set<Stmt> visited = new HashSet<>();
        Queue<Stmt> deque = new LinkedList<>();
        deque.add(cfg.getEntry());
        while (!deque.isEmpty()) {
            Stmt current = deque.poll();
            visited.add(current);
            if ((current instanceof If) || (current instanceof SwitchStmt)) {
                deque.addAll(cfg.getSuccsOf(current).stream().filter(stmt -> !deadCode.contains(stmt)).filter(stmt -> !visited.contains(stmt)).toList());
            } else {
                deque.addAll(cfg.getSuccsOf(current).stream().filter(stmt -> !visited.contains(stmt)).toList());
            }
        }

        deadCode.addAll(cfg.getNodes().stream().filter(stmt -> !visited.contains(stmt)).toList());
        // Non-interest
        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    private static void handleSwitch(Stmt stmt, DataflowResult<Stmt, CPFact> constants, CFG<Stmt> cfg, Set<Stmt> deadCode) {
        Var variable =  ((SwitchStmt) stmt).getVar();
        Value result = ConstantPropagation.evaluate(variable, constants.getOutFact(stmt));
        if (result.isConstant()) {
            int constantValue = result.getConstant();
            List<Integer> caseValues = ((SwitchStmt) stmt).getCaseValues();
            int currentCase = 0;
            boolean hasMatchedCase = false;
            for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                if (edge.getKind() == Edge.Kind.SWITCH_CASE) {
                    if (caseValues.get(currentCase) != constantValue) {
                        deadCode.add(edge.getTarget());
                    } else {
                        hasMatchedCase = true;
                    }
                    currentCase++;
                }
            }
            // Only add default branch when hasMatchedCase
            if (hasMatchedCase) {
                deadCode.add(((SwitchStmt) stmt).getDefaultTarget());
            }
        }
    }

    private static void handleIf(Stmt stmt, DataflowResult<Stmt, CPFact> constants, CFG<Stmt> cfg, Set<Stmt> deadCode) {
        ConditionExp condition = ((If) stmt).getCondition();
        Value result = ConstantPropagation.evaluate(condition, constants.getOutFact(stmt));

        if (result.equals(Value.makeConstant(1))) {
            // always true
            for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                if (edge.getKind() == Edge.Kind.IF_FALSE) {
                    deadCode.add(edge.getTarget());
                }
            }
        } else if (result.equals(Value.makeConstant(0))) {
            // always false
            for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                if (edge.getKind() == Edge.Kind.IF_TRUE) {
                    deadCode.add(edge.getTarget());
                }
            }
        }
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
