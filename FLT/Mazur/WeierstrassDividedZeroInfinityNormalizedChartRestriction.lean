/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedPairBase
public import FLT.Mazur.PolygonSmoothingPunctureSpecNaturality

/-!
# Full normalized chart maps commute with the original quotient

The entire original initial and infinity charts retain their coefficient squares
when the accumulated node correction is undone. Both infinity orientations agree.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "f" => fun k ↦ arithmeticZeroInfinityNormalizedInitial hπ data H k hj u hu
local notation "g" => fun k ↦ arithmeticZeroInfinityNormalizedBoundary hπ data H k hj u hu
local notation "T" => fun k ↦ arithmeticZeroDiagonalInitialTotalNodeIso hπ data H k hj u hu
local notation "V" => fun k ↦ arithmeticZeroDiagonalInfinityParameterIso hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "N" => closingNormalizedRestriction data H m
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m

omit [IsDomain R] [IsBezout R] in
/-- The reciprocal full boundary commutes with the original coefficient quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInversion_restriction :
    (edgeInversion (Q m)).hom ≫ ρ = ρ ≫ (edgeInversion (Q (m + 1))).hom :=
  (punctureSpecIso_naturality_iff (restriction R π m).toRingHom
    LaurentPolynomial.invert LaurentPolynomial.invert).mpr
      (punctureEquiv_invert_naturality _)

omit [IsDomain R] [IsBezout R] in
/-- The uncorrected whole right branch retains its complete coefficient square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRight_restriction :
    rightBranchOpen (Q m) (τ m) ≫ N = ρ ≫ rightBranchOpen (Q (m + 1)) (τ (m + 1)) :=
  factorRatioRightBranch_coefficient _ _ _ _

/-- Both full original initial opens follow the normalized whole-node quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedInitial_restriction (b : Bool) :
    S (.initial b) ≫ f (m + 1) b = f m b ≫ N := by
  apply (cancel_mono (T (m + 1) b).hom).mp
  simp only [arithmeticZeroInfinityNormalizedInitial, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [arithmeticZeroDiagonalAtlasRestriction_initial,
    arithmeticZeroDiagonalInitialFactorRatio_restriction,
    arithmeticZeroDiagonalInitialTotalNodeIso_restriction,
    Iso.inv_hom_id_assoc]

/-- Both full original infinity maps follow the same whole-node coefficient quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedBoundary_restriction (b : Bool) :
    S .infinity ≫ g (m + 1) b = g m b ≫ N := by
  cases b
  · simp only [arithmeticZeroInfinityNormalizedBoundary, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, Category.assoc, arithmeticZeroInfinityNormalizedRight_restriction]
    rw [arithmeticZeroDiagonalInfinityParameterIso_restriction_assoc]
  · simp only [arithmeticZeroInfinityNormalizedBoundary, ↓reduceIte, Category.assoc,
      arithmeticZeroInfinityNormalizedRight_restriction,
      arithmeticZeroInfinityNormalizedInversion_restriction_assoc]
    rw [arithmeticZeroDiagonalInfinityParameterIso_restriction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
