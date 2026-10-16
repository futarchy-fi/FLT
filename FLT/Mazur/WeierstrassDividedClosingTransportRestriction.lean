/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosingTransportGluing
public import FLT.Mazur.WeierstrassDividedRetainedClosingRestriction
public import FLT.Mazur.WeierstrassDividedFixedTerminalRestriction
public import FLT.Mazur.WeierstrassDividedRetainedChartRestriction

/-!
# Restriction of the transported original closing span

The transition is the ordered composite of the inverse retained parameter and
terminal parameter. Both original and transported boundaries follow the actual
coefficient restrictions, preserving the complete terminal smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => fun a ↦ Quotient R π a
local notation "τ" => fun a ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π a
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => fun a ↦ arithmeticTerminalSmoothing π a W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b4_div _) (H.b6_div _)

/-- The unchanged coefficient arrow on the original closing torus. -/
def closingOverlapRestriction : branchTorus (Q m) ⟶ branchTorus (Q (m + 1)) :=
  Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f))

/-- The unchanged coefficient arrow on the original retained node. -/
def closingRetainedRestriction :
    PolygonSmoothing.chart (Q m) (parameter R π m) ⟶
      PolygonSmoothing.chart (Q (m + 1)) (parameter R π (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap f _ _ (restriction_parameter R π m)))

/-- Both transported nodes use the fixed smoothing coefficient arrow. -/
def closingNormalizedRestriction :
    PolygonSmoothing.chart (Q m) (τ m) ⟶ PolygonSmoothing.chart (Q (m + 1)) (τ (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap f _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)))

/-- The original terminal node retains its full smoothing under restriction. -/
def closingTerminalRestriction :
    Spec (.of (NodalFiber.Coordinate (c m))) ⟶ Spec (.of (NodalFiber.Coordinate (c (m + 1)))) :=
  Spec.map (CommRingCat.ofHom (NodalFiber.coefficientRingMap f _ _
    (arithmeticTerminalSmoothing_restriction R π m W (π ^ (1 + j + 1))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
      (H.b4_div _) (H.b6_div _))))

local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "S" => closingRetainedRestriction (R := R) (π := π) m
local notation "N" => closingNormalizedRestriction data H m
local notation "D" => closingTerminalRestriction data H m j hj
local notation "L" => fun a ↦ arithmeticClosingRetainedBoundary data H a
local notation "v" => fun a ↦ arithmeticRetainedClosingUnit data H a (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "B" => fun a ↦ Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q a) (v a))))
local notation "C" => fun a ↦ arithmeticRetainedFixedSmoothingIso data H a (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))

/-- The retained source puncture follows the specified original coefficient map. -/
@[reassoc] theorem closingOriginalRetained_restriction :
    leftBranchOpen (Q m) (parameter R π m) ≫ S =
      ρ ≫ leftBranchOpen (Q (m + 1)) (parameter R π (m + 1)) :=
  leftBranchOpen_ringMap f _ _ (restriction_parameter R π m)

/-- The whole original terminal evaluation restricts on either branch. -/
@[reassoc] theorem closingOriginalTerminal_restriction (b : Bool) :
    arithmeticOriginalClosingBoundary data H m j hj b ≫ D =
      ρ ≫ arithmeticOriginalClosingBoundary data H (m + 1) j hj b :=
  (terminalArithmeticNodeEvaluation_restriction_square data m j hj H.a1_unit (H.scale j)
    H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) b).symm

include j hj in
/-- Transporting the retained square preserves the actual coefficient restriction. -/
@[reassoc] theorem closingTransportRetained_restriction :
    L m ≫ N = ρ ≫ L (m + 1) := by
  have hc : S ≫ (C (m + 1)).hom = (C m).hom ≫ N :=
    arithmeticRetainedFixedSmoothingIso_restriction data H m (j + 1) hj ⟨j, by omega⟩
  have hb : ρ ≫ B (m + 1) = B m ≫ ρ :=
    arithmeticRetainedClosingParameter_restriction data H m (j + 1) hj ⟨j, by omega⟩
  apply (cancel_epi (B m)).mp
  calc
    B m ≫ L m ≫ N = leftBranchOpen (Q m) (parameter R π m) ≫ (C m).hom ≫ N := by
      rw [← Category.assoc, ← arithmeticClosingSpan_retained, Category.assoc]
    _ = ρ ≫ leftBranchOpen (Q (m + 1)) (parameter R π (m + 1)) ≫ (C (m + 1)).hom := by
      rw [← hc, ← Category.assoc,
        closingOriginalRetained_restriction, Category.assoc]
    _ = B m ≫ ρ ≫ L (m + 1) := by
      rw [arithmeticClosingSpan_retained, ← Category.assoc,
        hb, Category.assoc]

variable [IsDomain R] (hπ : π ≠ 0)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
include hπ
local notation "T" => fun a b ↦ arithmeticClosingTerminalTwist data H a j hj u hu b
local notation "M" => fun a b ↦ arithmeticClosingTerminalBoundary data H a j hj u hu b

/-- The full transported transition follows restriction in its original composition order. -/
@[reassoc] theorem closingTransportTwist_restriction (b : Bool) :
    ρ ≫ (T (m + 1) b).hom = (T m b).hom ≫ ρ := by
  unfold closingOverlapRestriction
  simp only [arithmeticClosingTerminalTwist, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]
  rw [← Category.assoc, arithmeticRetainedClosingParameter_inv_restriction,
    Category.assoc, fixedTerminalPolygonBoundaryParameter_restriction R π m H.a1_unit hπ,
    ← Category.assoc]

/-- The inverse transition also follows the original quotient arrows. -/
@[reassoc] theorem closingTransportTwist_inv_restriction (b : Bool) :
    ρ ≫ (T (m + 1) b).inv = (T m b).inv ≫ ρ := by
  apply (cancel_mono (T (m + 1) b).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    closingTransportTwist_restriction data H m j hj hπ,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Both transported terminal punctures preserve the full normalized smoothing. -/
@[reassoc] theorem closingTransportTerminal_restriction (b : Bool) :
    M m b ≫ N = ρ ≫ M (m + 1) b := by
  simp only [arithmeticClosingTerminalBoundary, Category.assoc]
  have hb := fixedTerminalPolygonBranch_restriction R π m H.a1_unit b
  change _ ≫ closingNormalizedRestriction data H m = ρ ≫ _ at hb
  rw [hb, ← Category.assoc,
    ← closingTransportTwist_restriction data H m j hj hπ, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
