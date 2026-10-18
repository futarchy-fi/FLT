/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedExteriorEdges
public import FLT.Mazur.WeierstrassDividedZeroMobiusInitialIntersection
public import FLT.Mazur.PolygonVariableSmoothingEdgeIntersection

/-!
# The full initial fiber product of the independent revised target

The two full target initial nodes meet precisely along their Laurent edge.
This scheme-theoretic intersection retains every nilpotent function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
section Target
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "N" => 2 * (j + 1) + 3
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "c" => arithmeticRevisedPolygonInitialChart data H m j hj u hu
/-- The entire initial Laurent edge is the scheme-theoretic intersection of the target nodes. -/
theorem arithmeticRevisedPolygon_initial_isPullback :
    IsPullback (leftBranchOpen Q τ) (precedingBranch Q τ) (c true) (c false) := by
  have hn : initialPolygonIndex (j + 1) true ≠ initialPolygonIndex (j + 1) false := by
    intro he
    have hb := initialPolygonIndex_injective (j + 1) he
    contradiction
  exact PolygonVariableSmoothing.identifiedEdge_isPullback Q N p (by omega) _ _
    (initialPolygonIndex_preceding (j + 1)) hn
    (initialPolygonIndex_not_reverse_preceding (j + 1)) τ τ _ _

end Target

end FLT.Mazur.WeierstrassDividedDepth
