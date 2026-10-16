/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonComparisonCharts
public import FLT.Mazur.WeierstrassRetainedFixedTerminalEdges

/-!
# The exact remaining closing condition for the complete polygon comparison

All original atlas pairs are compatible precisely when both transported
terminal twists are identities. This criterion retains the complete Laurent
parameters, not only their residues or tangent coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π m H.scale_div)
local notation "F" => arithmeticPolygonComparisonChart hπ data H m j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "last" => fun b ↦ ArithmeticChartLabel.retained (Fin.mk j (Nat.lt_succ_self j)) b
local notation "l" => leftBranchOpen Q (parameter R π m)
local notation "r" => arithmeticOriginalClosingBoundary data H m j hj
local notation "v" => arithmeticRetainedClosingUnit data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) v)))
local notation "T" => fixedTerminalPolygonBoundaryParameter data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
local notation "P" => PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega) 0
local notation "puncture" => fun (opposite : Bool) ↦
  ite (opposite = true) (leftBranchOpen Q τ) (rightBranchOpen Q τ)

omit [IsBezout R] in
/-- The last retained chart reaches polygon label zero with the entire reciprocal parameter. -/
@[reassoc] theorem arithmeticPolygonComparisonChart_last (b : Bool) :
    let _ := hn
    l ≫ F (last b) = B ≫ puncture b ≫ P := by
  let _ := hn
  exact retainedFixedPolygonMap_last (parameter R π m) τ
    (arithmeticStartOneQuotient W H.a1_unit π m)
    (arithmeticStartOneQuotient_relation W H.a1_unit π m) 1 j
    (arithmeticRetainedFullCorrection data H m (j + 1) hj ⟨j, Nat.lt_succ_self j⟩) b

omit [IsBezout R] in
/-- The actual full terminal comparison keeps its independently constructed boundary parameter. -/
@[reassoc] theorem arithmeticPolygonComparisonChart_terminal (b : Bool) :
    let _ := hn
    r b ≫ F .terminal = T b ≫ puncture b ≫ P := by
  let _ := hn
  change r b ≫ _ ≫ P = _
  dsimp only [twistedArithmeticAtlasIso, arithmeticOriginalClosingBoundary]
  rw [← Category.assoc, fixedTerminalPolygon_boundary, Category.assoc]

/-- One full terminal fiber-product equation is exactly equality of the two actual parameters. -/
theorem arithmeticPolygonComparisonChart_closing_iff (b : Bool) :
    pullback.fst (c .terminal) (c (last b)) ≫ F .terminal =
      pullback.snd (c .terminal) (c (last b)) ≫ F (last b) ↔ B = T b := by
  let _ := hn
  have hp := (originalClosingAttachment_isPullback hπ data H m j hj b).flip
  rw [← cancel_epi hp.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  rw [arithmeticPolygonComparisonChart_terminal, arithmeticPolygonComparisonChart_last]
  have hi : IsOpenImmersion (puncture b) := by cases b <;> dsimp <;> infer_instance
  rw [← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono]
  exact eq_comm

omit [IsDomain R] [IsBezout R] in
/-- The transported closing twist is trivial exactly when the original full parameters agree. -/
theorem arithmeticClosingTerminalTwist_eq_id_iff (b : Bool) :
    (arithmeticClosingTerminalTwist data H m j hj u hu b).hom = 𝟙 _ ↔ B = T b := by
  change inv B ≫ T b = 𝟙 _ ↔ B = T b
  rw [← cancel_epi B]
  simp only [IsIso.hom_inv_id_assoc, Category.comp_id]
  exact eq_comm

/-- Every original chart pair is compatible exactly when both complete terminal twists vanish. -/
theorem arithmeticPolygonComparisonChart_full_iff :
    (∀ a b, pullback.fst (c a) (c b) ≫ F a = pullback.snd (c a) (c b) ≫ F b) ↔
      ∀ b, (arithmeticClosingTerminalTwist data H m j hj u hu b).hom = 𝟙 _ := by
  rw [arithmeticPolygonComparisonChart_compatible_iff,
    arithmeticPositiveTerminal_compatible_iff]
  apply forall_congr'
  intro b
  exact (arithmeticPolygonComparisonChart_closing_iff hπ data H m j hj u hu b).trans
    (arithmeticClosingTerminalTwist_eq_id_iff data H m j hj u hu b).symm

end FLT.Mazur.WeierstrassDividedDepth
