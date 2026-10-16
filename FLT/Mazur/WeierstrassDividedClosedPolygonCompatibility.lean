/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedTerminalNormalization
public import FLT.Mazur.WeierstrassDividedPolygonClosingCriterion

/-!
# Compatible polygon charts on the complete original closed arithmetic stage

The exterior comparison is retained verbatim. One full terminal automorphism
corrects both original closing edges, so every original chart pair agrees.
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
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 0 H.scale_div)
local notation "Y" => arithmeticFactorRatioPolygon π 0 W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)
local notation "A" => arithmeticLabeledAtlasObject hπ data H 0 (j + 1) hj
local notation "e" => twistedArithmeticAtlasIso hπ data H 0 j hj u hu
local notation "N" => arithmeticClosedTerminalNormalization data H j hj u hu
local notation "F" => arithmeticPolygonComparisonChart hπ data H 0 j hj u hu

/-- Correct only the whole terminal comparison, retaining all original exterior chart maps. -/
def arithmeticClosedPolygonComparisonChart (i : ArithmeticChartLabel (j + 1)) : A i ⟶ Y := by
  let _ := hn
  exact match i with
  | .terminal => (e .terminal).hom ≫ (N).hom ≫
      PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega) 0
  | .infinity => F .infinity
  | .initial b => F (.initial b)
  | .retained a b => F (.retained a b)

local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "last" => fun b ↦ ArithmeticChartLabel.retained (Fin.mk j (Nat.lt_succ_self j)) b
local notation "r" => arithmeticOriginalClosingBoundary data H 0 j hj
local notation "v" => arithmeticRetainedClosingUnit data H 0 (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) v)))
local notation "T" => fixedTerminalPolygonBoundaryParameter data 0 j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
local notation "P" => PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega) 0
local notation "puncture" => fun (b : Bool) ↦
  ite (b = true) (leftBranchOpen Q τ) (rightBranchOpen Q τ)

/-- The unchanged infinity equations remain valid. -/
theorem arithmeticClosedPolygonComparisonChart_infinity :
    arithmeticInitialInfinityCompatible hπ data H 0 (j + 1) hj G :=
  arithmeticPolygonComparisonChart_infinity hπ data H 0 j hj u hu

omit [IsBezout R] in
/-- Both original first-edge equations are preserved by the simultaneous correction. -/
theorem arithmeticClosedPolygonComparisonChart_initial :
    arithmeticPositiveInitialCompatible hπ data H 0 j hj G :=
  arithmeticPolygonComparisonChart_initial hπ data H 0 j hj u hu

omit [IsBezout R] in
/-- Every retained edge keeps its original full correction and label. -/
theorem arithmeticClosedPolygonComparisonChart_adjacent :
    arithmeticPositiveAdjacentCompatible hπ data H 0 j hj G :=
  arithmeticPolygonComparisonChart_adjacent hπ data H 0 j hj u hu

omit [IsBezout R] in
/-- Both actual terminal boundaries now have exactly the retained closing parameter. -/
@[reassoc] theorem arithmeticClosedPolygonComparisonChart_terminal (b : Bool) :
    let _ := hn
    r b ≫ G .terminal = B ≫ puncture b ≫ P := by
  let _ := hn
  have hr : r b ≫ (e .terminal).hom = T b ≫ puncture b := by
    dsimp only [twistedArithmeticAtlasIso, arithmeticOriginalClosingBoundary]
    exact fixedTerminalPolygon_boundary ..
  change r b ≫ (e .terminal).hom ≫ (N).hom ≫ P = _
  rw [← Category.assoc (r b), hr]
  simpa only [Category.assoc] using
    arithmeticClosedTerminalNormalization_corrected_assoc data H j hj u hu b P

/-- The two full original terminal fiber products satisfy the corrected closing equations. -/
theorem arithmeticClosedPolygonComparisonChart_closing (b : Bool) :
    pullback.fst (c .terminal) (c (last b)) ≫ G .terminal =
      pullback.snd (c .terminal) (c (last b)) ≫ G (last b) := by
  let _ := hn
  have hp := (originalClosingAttachment_isPullback hπ data H 0 j hj b).flip
  rw [← cancel_epi hp.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  rw [arithmeticClosedPolygonComparisonChart_terminal]
  exact (arithmeticPolygonComparisonChart_last hπ data H 0 j hj u hu b).symm

/-- Both original terminal edge conditions now hold without an equality assumption on twists. -/
theorem arithmeticClosedPolygonComparisonChart_terminalCompatible :
    arithmeticPositiveTerminalCompatible hπ data H 0 j hj G :=
  (arithmeticPositiveTerminal_compatible_iff hπ data H 0 j hj G).mpr
    (arithmeticClosedPolygonComparisonChart_closing hπ data H j hj u hu)

/-- Every ordered pair agrees on its full original chart intersection. -/
theorem arithmeticClosedPolygonComparisonChart_compatible :
    ∀ a b, pullback.fst (c a) (c b) ≫ G a = pullback.snd (c a) (c b) ≫ G b :=
  arithmeticPositiveLabeled_compatible hπ data H 0 j hj G
    (arithmeticClosedPolygonComparisonChart_infinity hπ data H j hj u hu)
    (arithmeticClosedPolygonComparisonChart_initial hπ data H j hj u hu)
    (arithmeticClosedPolygonComparisonChart_adjacent hπ data H j hj u hu)
    (arithmeticClosedPolygonComparisonChart_terminalCompatible hπ data H j hj u hu)

end FLT.Mazur.WeierstrassDividedDepth
