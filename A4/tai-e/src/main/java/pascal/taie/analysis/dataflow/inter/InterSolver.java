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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        Set<Node> entryNodeSet = new HashSet<>();
        icfg.entryMethods().forEach(method -> {
            Node entryNode = icfg.getEntryOf(method);
            entryNodeSet.add(entryNode);
            result.setInFact(entryNode, analysis.newInitialFact());
            result.setOutFact(entryNode, analysis.newBoundaryFact(entryNode));
        });
        for (Node node : icfg) {
            if (!entryNodeSet.contains(node)) {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        }
    }

    private void doSolve() {
        Queue<Node> worklist = new LinkedList<>(icfg.getNodes());
        while (!worklist.isEmpty()) {
            Node current = worklist.poll();
            // System.out.println("==================");
            // System.out.println("Handling " + current);

            // System.out.println("Before: " + result.getInFact(current));
            for (ICFGEdge<Node> edge : icfg.getInEdgesOf(current)) {
                // System.out.println("\t" + "handling: " + edge);
                Fact newOut = analysis.transferEdge(edge, result.getOutFact(edge.getSource()));
                analysis.meetInto(newOut, result.getInFact(current));
            }
            // System.out.println("meet: " + result.getInFact(current));

            if (analysis.transferNode(current, result.getInFact(current), result.getOutFact(current))) {
                worklist.addAll(icfg.getSuccsOf(current));
            }
            // System.out.println("final: " + result.getInFact(current));
        }
    }
}
