/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFields

/-!
# The two actual edges incident to each retained node

The incoming and outgoing indices share the same retained node. Boundary nodes
use the original initial or closing edge; depth zero has no internal edge.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticRetainedChain
variable {n : ℕ}

/-- The first node receives the initial edge; every later node receives an internal edge. -/
def incomingEdge (i : Fin (n + 1)) : Edge n :=
  Fin.cases .initial (fun j ↦ .incoming j) i

/-- The last node supplies the closing edge; every earlier node supplies an internal edge. -/
def outgoingEdge (i : Fin (n + 1)) : Edge n :=
  Fin.lastCases .closing (fun j ↦ .incoming j) i

/-- The original initial edge meets the first retained node. -/
theorem incomingEdge_zero : incomingEdge (0 : Fin (n + 1)) = .initial := rfl

/-- Each internal edge meets its successor node on the incoming side. -/
theorem incomingEdge_succ (i : Fin n) : incomingEdge i.succ = .incoming i := rfl

/-- The final outgoing edge is the original closing edge. -/
theorem outgoingEdge_last : outgoingEdge (Fin.last n) = .closing := by
  simp [outgoingEdge]

/-- Each internal edge leaves its predecessor node on the outgoing side. -/
theorem outgoingEdge_castSucc (i : Fin n) : outgoingEdge i.castSucc = .incoming i := by
  simp [outgoingEdge]

/-- The internal edge is literally the same edge at both of its endpoints. -/
theorem internalEdge_shared (i : Fin n) : outgoingEdge i.castSucc = incomingEdge i.succ := by
  rw [outgoingEdge_castSucc, incomingEdge_succ]

end FLT.Mazur.PolygonArithmeticRetainedChain
