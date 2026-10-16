/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapInfinityIso
public import FLT.Mazur.WeierstrassModificationXNodeOverlapRatio

/-!
# An explicit ring map for the entire original infinity overlap

The original y remains a unit on the complete node intersection at arbitrary
nilpotent order. Its localization lift is exactly the pre-existing geometric
infinity isomorphism, preserving every original initial coordinate.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "O" => PolynomialNodeOverlap W s
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "G" => polynomialNodeOverlapEvaluation W s b3 b4 b6 r hr I hI hrI h3
local notation "V" => polynomialSmallFactor W s b3 b4 b6 r
local notation "U" => polynomialOppositeFactor W s b3 b4 b6 r

/-- The full original slope is a unit on the entire original node overlap. -/
theorem polynomialNodeOverlap_slope_isUnit : IsUnit (G (v W s b3 b4 b6)) := by
  have hn := (NilpotentQuadraticRoot.element_nilpotent (I.map C)
    (polynomialArithmeticIdeal_nilpotent I hI) hrI).map
      ((G).toRingHom.comp (algebraMap R[X] A))
  have hu := hn.isUnit_add_left_of_commute
    (polynomialNodeOverlap_small_isUnit W s b3 b4 b6 r hr I hI hrI h3) (mul_comm _ _)
  convert hu using 1
  simp only [RingHom.comp_apply, polynomialSmallFactor, map_sub]
  change G (v W s b3 b4 b6) = G (v W s b3 b4 b6) -
    G (algebraMap R[X] A r) + G (algebraMap R[X] A r)
  ring

/-- The entire original node overlap inverts the original y at every arithmetic order. -/
theorem polynomialNodeOverlap_y_isUnit : IsUnit (G (y W s b3 b4 b6)) := by
  rw [y, map_mul, polynomialFactors_horizontal W s b3 b4 b6 r hr, map_mul]
  exact ((polynomialNodeOverlap_small_isUnit W s b3 b4 b6 r hr I hI hrI h3).mul
    (polynomialNodeOverlap_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3)).mul
      (polynomialNodeOverlap_slope_isUnit W s b3 b4 b6 r hr I hI hrI h3)

/-- The explicit full infinity localization lift of the original node-overlap evaluation. -/
def polynomialNodeOverlapInfinityEvaluation : Y →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (y W s b3 b4 b6) (f := G)
    (polynomialNodeOverlap_y_isUnit W s b3 b4 b6 r hr I hI hrI h3)

/-- The lift preserves every original affine function, including all nilpotent corrections. -/
theorem polynomialNodeOverlapInfinityEvaluation_base (z : A) :
    polynomialNodeOverlapInfinityEvaluation W s b3 b4 b6 r hr I hI hrI h3
      (algebraMap A Y z) = G z := by
  rw [polynomialNodeOverlapInfinityEvaluation, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The constructed ring map is precisely the original full geometric infinity isomorphism. -/
theorem polynomialNodeOverlapInfinityIso_hom_eq_spec :
    (polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI h3).hom =
      Spec.map (CommRingCat.ofHom
        (polynomialNodeOverlapInfinityEvaluation W s b3 b4 b6 r hr I hI hrI h3).toRingHom) := by
  apply (cancel_mono (polynomialInitialInfinityInclusion W s b3 b4 b6)).mp
  rw [polynomialNodeOverlapInfinityIso_hom_inclusion, polynomialNodeOverlapEvaluation_spec,
    polynomialInitialInfinityInclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun z =>
    (polynomialNodeOverlapInfinityEvaluation_base W s b3 b4 b6 r hr I hI hrI h3 z).symm

end FLT.Mazur.WeierstrassModificationX
