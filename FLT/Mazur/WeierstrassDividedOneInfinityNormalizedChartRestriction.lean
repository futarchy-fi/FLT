/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedPairBase
public import FLT.Mazur.PolygonSmoothingPunctureSpecNaturality
public import FLT.Mazur.WeierstrassDividedOneDiagonalInfinityRestriction
public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioRestriction

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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "f" => fun k ↦ arithmeticOneInfinityNormalizedInitial hπ data H k hj u hu
local notation "g" => fun k ↦ arithmeticOneInfinityNormalizedBoundary hπ data H k hj u hu
local notation "E" => fun k ↦ arithmeticOneDiagonalInitialTotalOpenIso hπ data H k hj u hu
local notation "V" => fun k ↦ arithmeticOneDiagonalInfinityParameterIso hπ data H k hj u hu
local notation "S" => arithmeticOneDiagonalAtlasRestriction hπ data H hj u hu m
local notation "N" => closingNormalizedRestriction data H m
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m

omit [IsDomain R] [IsBezout R] in
/-- The reciprocal full boundary commutes with the original coefficient quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedInversion_restriction :
    (edgeInversion (Q m)).hom ≫ ρ = ρ ≫ (edgeInversion (Q (m + 1))).hom :=
  (punctureSpecIso_naturality_iff (restriction R π m).toRingHom
    LaurentPolynomial.invert LaurentPolynomial.invert).mpr
      (punctureEquiv_invert_naturality _)

omit [IsDomain R] [IsBezout R] in
/-- The uncorrected whole right branch retains its complete coefficient square. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRight_restriction :
    rightBranchOpen (Q m) (τ m) ≫ N = ρ ≫ rightBranchOpen (Q (m + 1)) (τ (m + 1)) :=
  factorRatioRightBranch_coefficient _ _ _ _

/-- The complete original initial-open transport follows its actual coefficient quotient. -/
@[reassoc] theorem arithmeticOneDiagonalInitialTotalOpenIso_restriction (b : Bool) :
    (E m b).hom ≫ S (.initial b) =
      arithmeticFullInitialNodeQuotient R π m W (π ^ 1) ≫ (E (m + 1) b).hom := by
  change (arithmeticOneFiniteInitialTotalOpenIso hπ data H m hj u hu m b).hom ≫ _ =
    _ ≫ (arithmeticOneFiniteInitialTotalOpenIso hπ data H (m + 1) hj u hu (m + 1) b).hom
  rw [arithmeticOneFiniteInitialTotalOpenIso_atlas,
    arithmeticOneFiniteInitialTotalOpenIso_atlas, arithmeticOneDiagonalFullAtlasIso_restriction]
  rfl

/-- Both full original initial opens follow the normalized whole-node quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedInitial_restriction (b : Bool) :
    S (.initial b) ≫ f (m + 1) b = f m b ≫ N := by
  apply (cancel_epi (E m b).hom).mp
  rw [arithmeticOneInfinityNormalizedInitial_transport_assoc]
  rw [← Category.assoc, arithmeticOneDiagonalInitialTotalOpenIso_restriction,
    Category.assoc, arithmeticOneInfinityNormalizedInitial_transport]
  exact arithmeticInitialFactorRatioChart_closingRestriction data H m

/-- Both full original infinity maps follow the same whole-node coefficient quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedBoundary_restriction (b : Bool) :
    S .infinity ≫ g (m + 1) b = g m b ≫ N := by
  cases b
  · simp only [arithmeticOneInfinityNormalizedBoundary, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, Category.assoc, arithmeticOneInfinityNormalizedRight_restriction]
    rw [arithmeticOneDiagonalInfinityParameterIso_restriction_assoc]
  · simp only [arithmeticOneInfinityNormalizedBoundary, ↓reduceIte, Category.assoc,
      arithmeticOneInfinityNormalizedRight_restriction,
      arithmeticOneInfinityNormalizedInversion_restriction_assoc]
    rw [arithmeticOneDiagonalInfinityParameterIso_restriction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
