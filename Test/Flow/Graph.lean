-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import S2IL.Flow

/-!
# Test.Flow.Graph

FlowGraph の初期 well-formed 判定テスト。
-/

open S2IL

namespace Test.Flow.Graph

private def amount1 : FlowAmount := { units := 1 }

private def beltThroughput : Throughput :=
  { kind := StreamKind.belt, amount := amount1 }

private def beltCapacity : Capacity :=
  { kind := StreamKind.belt, amount := amount1 }

private def capability : Capability :=
  { throughput := beltThroughput,
    inputCapacity := beltCapacity,
    outputCapacity := beltCapacity,
    requires := [], consumes := [], produces := [] }

private def node (id : NodeId) (kind : MachineKind) : MachineNode :=
  { id := id, spec := kind.machineSpec capability }

private def edge (sourceNode sourcePort targetNode targetPort : Nat) : FlowEdge :=
  { source := { node := sourceNode, port := sourcePort },
    target := { node := targetNode, port := targetPort } }

-- ============================================================
-- port lookup
-- ============================================================

private def rotatorNode : MachineNode := node 0 MachineKind.rotator
private def painterNode : MachineNode := node 1 MachineKind.painter
private def mixerNode : MachineNode := node 1 MachineKind.colorMixer

#guard rotatorNode.outputPort? 0 == some (PortSpec.belt "output")
#guard rotatorNode.outputPort? 1 == none
#guard painterNode.inputPort? 0 == some (PortSpec.belt "shape")
#guard painterNode.inputPort? 1 == some (PortSpec.pipe "fluid")

example : rotatorNode.outputPort? 0 = rotatorNode.spec.ports.outputs[0]? :=
  MachineNode.outputPort?_eq_getElem? rotatorNode 0

example : painterNode.inputPort? 1 = painterNode.spec.ports.inputs[1]? :=
  MachineNode.inputPort?_eq_getElem? painterNode 1

-- ============================================================
-- valid representative graph
-- ============================================================

private def rotatorToPainter : FlowEdge := edge 0 0 1 0

private def validGraph : FlowGraph :=
  { nodes := [rotatorNode, painterNode], edges := [rotatorToPainter] }

#guard validGraph.nodeIdsUnique
#guard validGraph.edgePortsExist rotatorToPainter
#guard validGraph.edgeKindsMatch rotatorToPainter
#guard validGraph.edgeRespectsNodeOrder rotatorToPainter
#guard validGraph.acyclic
#guard validGraph.wellFormed

example : FlowGraph.WellFormed validGraph := rfl

example : validGraph.edgePortsExist rotatorToPainter = true :=
  FlowGraph.edgePortsExist_eq_true_of_output_input rfl rfl

example : validGraph.edgeKindsMatch rotatorToPainter = true :=
  FlowGraph.edgeKindsMatch_eq_true_of_output_input rfl rfl rfl

-- ============================================================
-- invalid graph cases
-- ============================================================

private def kindMismatchEdge : FlowEdge := edge 0 0 1 0

private def kindMismatchGraph : FlowGraph :=
  { nodes := [rotatorNode, mixerNode], edges := [kindMismatchEdge] }

#guard kindMismatchGraph.edgePortsExist kindMismatchEdge
#guard !kindMismatchGraph.edgeKindsMatch kindMismatchEdge
#guard !kindMismatchGraph.wellFormed

private def missingPortEdge : FlowEdge := edge 0 1 1 0

private def missingPortGraph : FlowGraph :=
  { nodes := [rotatorNode, painterNode], edges := [missingPortEdge] }

#guard !missingPortGraph.edgePortsExist missingPortEdge
#guard !missingPortGraph.wellFormed

private def backwardEdge : FlowEdge := edge 1 0 0 0

private def backwardGraph : FlowGraph :=
  { nodes := [rotatorNode, painterNode], edges := [backwardEdge] }

#guard backwardGraph.edgePortsExist backwardEdge
#guard backwardGraph.edgeKindsMatch backwardEdge
#guard !backwardGraph.edgeRespectsNodeOrder backwardEdge
#guard backwardGraph.acyclic
#guard backwardGraph.wellFormed

private def cycleBackEdge : FlowEdge := edge 1 0 0 0

private def cyclicGraph : FlowGraph :=
  { nodes := [rotatorNode, painterNode], edges := [rotatorToPainter, cycleBackEdge] }

#guard cyclicGraph.edgePortsExist cycleBackEdge
#guard cyclicGraph.edgeKindsMatch cycleBackEdge
#guard cyclicGraph.hasCycle
#guard !cyclicGraph.acyclic
#guard !cyclicGraph.wellFormed

private def selfLoopEdge : FlowEdge := edge 0 0 0 0

private def selfLoopGraph : FlowGraph :=
  { nodes := [rotatorNode], edges := [selfLoopEdge] }

#guard selfLoopGraph.edgePortsExist selfLoopEdge
#guard selfLoopGraph.edgeKindsMatch selfLoopEdge
#guard selfLoopGraph.hasCycle
#guard !selfLoopGraph.acyclic
#guard !selfLoopGraph.wellFormed

private def duplicateIdGraph : FlowGraph :=
  { nodes := [node 0 MachineKind.rotator, node 0 MachineKind.painter], edges := [] }

#guard !duplicateIdGraph.nodeIdsUnique
#guard !duplicateIdGraph.wellFormed

-- ============================================================
-- cutter -> rotator representative flow
-- ============================================================

private def cutterNode : MachineNode := node 0 MachineKind.cutter
private def downstreamRotator : MachineNode := node 1 MachineKind.rotator
private def cutterToRotator : FlowEdge := edge 0 0 1 0

private def cutterRotateGraph : FlowGraph :=
  { nodes := [cutterNode, downstreamRotator], edges := [cutterToRotator] }

#guard cutterRotateGraph.edgeKindsMatch cutterToRotator
#guard cutterRotateGraph.wellFormed

end Test.Flow.Graph
