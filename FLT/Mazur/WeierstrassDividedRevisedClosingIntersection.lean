/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedPolygonEdges
public import FLT.Mazur.PolygonVariableSmoothingEdgeIntersection

/-!
# Exact closing fiber products in the revised arithmetic polygon

Both closing pairs have their whole Laurent edge as intersection. The proof
uses the independent cyclic atlas and rules out the reverse edge explicitly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "N" => 2 * (j + 1) + 3
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "c" => arithmeticRevisedPolygonRetainedChart data H m j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "O" => twistedRetainedOrientation data H m
local notation "i" => retainedPolygonIndex (j + 1) (Fin.mk j (Nat.lt_succ_self j)) false
local notation "k" => retainedPolygonIndex (j + 1) (Fin.mk j (Nat.lt_succ_self j)) true

/-- The two closing arms retain distinct cyclic labels. -/
theorem revisedPolygon_last_labels_ne (r : ℕ) :
    retainedPolygonIndex (r + 1) (Fin.mk r (Nat.lt_succ_self r)) true ≠
      retainedPolygonIndex (r + 1) (Fin.mk r (Nat.lt_succ_self r)) false := by
  intro he
  have hv := congrArg Fin.val he
  simp only [retainedPolygonIndex, Bool.false_eq_true, ↓reduceIte] at hv
  omega

/-- The first-arm closing has precisely its full standard edge as fiber product. -/
theorem arithmeticRevisedPolygon_closing_false_isPullback :
    IsPullback L (rightBranchOpen Q σ) (c ⟨j, by omega⟩ false) d := by
  have hn : (finRotate N).symm 0 ≠ i := by
    rw [retainedPolygonIndex_true_terminal]
    exact revisedPolygon_last_labels_ne j
  have he : IsPullback (leftBranchOpen Q τ) (precedingBranch Q σ)
      (c ⟨j, by omega⟩ false) d :=
    PolygonVariableSmoothing.identifiedEdge_isPullback Q N p (by omega) i 0
      (retainedPolygonIndex_false_terminal j) (retainedPolygonIndex_ne_terminal _ _ _) hn
      τ σ _ _
  exact PolygonVariableSmoothing.inverseEdge_isPullback Q τ σ _ _ he

/-- The opposite closing has the other full puncture of the same terminal as fiber product. -/
theorem arithmeticRevisedPolygon_closing_true_isPullback :
    IsPullback L (leftBranchOpen Q σ) ((O true).hom ≫ c ⟨j, by omega⟩ true) d := by
  have hn : (finRotate N).symm k ≠ 0 := by
    intro he
    exact revisedPolygon_last_labels_ne j
      ((finRotate N).symm.injective (he.trans (retainedPolygonIndex_false_terminal j).symm))
  have he : IsPullback (leftBranchOpen Q σ) (precedingBranch Q τ)
      d (c ⟨j, by omega⟩ true) :=
    PolygonVariableSmoothing.identifiedEdge_isPullback Q N p (by omega) 0 k
      (retainedPolygonIndex_true_terminal j) (retainedPolygonIndex_ne_terminal _ _ _).symm hn
      σ τ _ _
  exact PolygonVariableSmoothing.swappedEdge_isPullback Q τ σ _ _ he.flip

/-- Both original retained orientations give the exact full closing fiber product. -/
theorem arithmeticRevisedPolygon_closing_isPullback (b : Bool) :
    IsPullback L (if b then leftBranchOpen Q σ else rightBranchOpen Q σ)
      ((O b).hom ≫ c ⟨j, by omega⟩ b) d := by
  cases b
  · change IsPullback L (rightBranchOpen Q σ) (𝟙 _ ≫ c ⟨j, by omega⟩ false) d
    rw [Category.id_comp]
    exact arithmeticRevisedPolygon_closing_false_isPullback data H m j hj u hu
  · exact arithmeticRevisedPolygon_closing_true_isPullback data H m j hj u hu

end FLT.Mazur.WeierstrassDividedDepth
