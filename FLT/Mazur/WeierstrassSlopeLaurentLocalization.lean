/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXSlopeOpen
public import FLT.Mazur.WeierstrassInfinityLaurentPuncture

/-!
# The two-root slope open is the Laurent torus punctured at one

The mutually inverse substitutions are T=(v+a)/v and v=a/(T-1).
These are equivalences of the full localized algebras over any base ring
with a unit tangent coefficient, including their coefficient structures.
-/

@[expose] public noncomputable section
open Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [CommRing K] (a : Kˣ)
local notation "P" => SlopeOpen (a : K)
local notation "L" => WeierstrassIntegralChart.LaurentPuncture K
local notation "z" => slopeZ (a : K)
local notation "A" => algebraMap K P (a : K)
local notation "t" => algebraMap K[T;T⁻¹] L (LaurentPolynomial.T 1)
local notation "B" => algebraMap K L (a : K)
local notation "r" => (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹])

local instance slopeLaurentTower : IsScalarTower K K[X] K[T;T⁻¹] :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (Polynomial.toLaurent_C x).symm)

/-- The ordered ratio of the two tangent factors is a unit on the full slope open. -/
def slopeLaurentUnit : Pˣ :=
  (slope_units (a : K)).2.1.unit * (slope_units (a : K)).1.unit⁻¹

/-- Substitute the ordered tangent ratio into the entire Laurent algebra. -/
def slopeLaurentMap : K[T;T⁻¹] →ₐ[K] P :=
  IsLocalization.Away.liftAlgHom (f := aeval (slopeLaurentUnit a : P)) X
    (by rw [aeval_X]; exact Units.isUnit _)

/-- The positive Laurent generator retains the original ordered tangent ratio. -/
theorem slopeLaurentMap_T : slopeLaurentMap a (LaurentPolynomial.T 1) =
    (z + A) * ↑(slope_units (a : K)).1.unit⁻¹ := by
  rw [← Polynomial.toLaurent_X]
  change slopeLaurentMap a (algebraMap K[X] K[T;T⁻¹] X) = _
  rw [slopeLaurentMap, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
  exact congrArg (fun w : P => w * (↑(slope_units (a : K)).1.unit⁻¹ : P))
    (slope_units (a : K)).2.1.unit_spec

/-- Subtracting one from the tangent ratio leaves a/v. -/
theorem slopeLaurentMap_sub_one : slopeLaurentMap a r =
    A * ↑(slope_units (a : K)).1.unit⁻¹ := by
  rw [map_sub, map_one, slopeLaurentMap_T, add_mul,
    Units.mul_inv_eq_one.mpr (slope_units (a : K)).1.unit_spec]
  ring

/-- The inverse slope substitution on the torus punctured at one. -/
def punctureSlope : L := B * IsLocalization.Away.invSelf r

/-- The inverse substitution retains its exact denominator. -/
theorem punctureSlope_mul : punctureSlope a * (t - 1) = B := by
  rw [punctureSlope, mul_assoc, ← map_one (algebraMap K[T;T⁻¹] L), ← map_sub,
    mul_comm (IsLocalization.Away.invSelf r), IsLocalization.Away.mul_invSelf, mul_one]

/-- The second tangent factor is the first one times the original Laurent parameter. -/
theorem punctureSlope_add : punctureSlope a + B = punctureSlope a * t := by
  have h := punctureSlope_mul a
  rw [mul_sub, mul_one] at h
  linear_combination -h

/-- Both tangent factors are units everywhere on the full Laurent puncture. -/
theorem punctureSlope_units : IsUnit (punctureSlope a) ∧ IsUnit (punctureSlope a + B) := by
  have hv : IsUnit (punctureSlope a) :=
    (a.isUnit.map (algebraMap K L)).mul
      (isUnit_of_mul_isUnit_right (show IsUnit
        (algebraMap K[T;T⁻¹] L r * IsLocalization.Away.invSelf r) from
          (IsLocalization.Away.mul_invSelf (S := L) r).symm ▸ isUnit_one))
  refine ⟨hv, ?_⟩
  rw [punctureSlope_add]
  exact hv.mul ((LaurentPolynomial.isUnit_T (R := K) 1).map (algebraMap K[T;T⁻¹] L))

/-- The full slope localization maps back to the punctured Laurent torus. -/
def slopeToLaurentPuncture : P →ₐ[K] L :=
  IsLocalization.Away.liftAlgHom (f := aeval (punctureSlope a)) (slopePolynomial (a : K))
    (by simpa only [slopePolynomial, map_mul, map_add, aeval_X, aeval_C] using
      (punctureSlope_units a).1.mul (punctureSlope_units a).2)

/-- The inverse map preserves the named original slope generator. -/
theorem slopeToLaurentPuncture_z : slopeToLaurentPuncture a z = punctureSlope a := by
  rw [slopeZ, slopeToLaurentPuncture, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, aeval_X]

/-- The Laurent transition extends over the entire puncture at one. -/
def laurentPunctureToSlope : L →ₐ[K] P :=
  IsLocalization.Away.liftAlgHom (f := slopeLaurentMap a) r (by
    rw [slopeLaurentMap_sub_one]
    exact (a.isUnit.map (algebraMap K P)).mul (Units.isUnit _))

/-- The puncture extension retains every Laurent function. -/
theorem laurentPunctureToSlope_base (w : K[T;T⁻¹]) :
    laurentPunctureToSlope a (algebraMap K[T;T⁻¹] L w) = slopeLaurentMap a w := by
  rw [laurentPunctureToSlope, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The original slope is recovered from the inverse rational substitution. -/
theorem laurentPunctureToSlope_parameter :
    laurentPunctureToSlope a (punctureSlope a) = z := by
  have h := congrArg (laurentPunctureToSlope a) (punctureSlope_mul a)
  rw [map_mul, map_sub, map_one, laurentPunctureToSlope_base, AlgHom.commutes,
    ← map_one (slopeLaurentMap a), ← map_sub, slopeLaurentMap_sub_one] at h
  apply ((a.isUnit.map (algebraMap K P)).mul
    (Units.isUnit (slope_units (a : K)).1.unit⁻¹)).mul_right_cancel
  rw [h]
  calc
    A = A * (z * ↑(slope_units (a : K)).1.unit⁻¹) := by
      rw [Units.mul_inv_eq_one.mpr (slope_units (a : K)).1.unit_spec, mul_one]
    _ = _ := by ring

/-- The reverse substitution recovers the original Laurent generator. -/
theorem slopeToLaurentPuncture_T :
    slopeToLaurentPuncture a (slopeLaurentMap a (LaurentPolynomial.T 1)) = t := by
  apply (punctureSlope_units a).1.mul_right_cancel
  rw [← slopeToLaurentPuncture_z, ← map_mul, slopeLaurentMap_T, mul_assoc,
    Units.inv_mul_eq_one.mpr (slope_units (a : K)).1.unit_spec, mul_one,
    map_add, slopeToLaurentPuncture_z, AlgHom.commutes, punctureSlope_add]
  exact mul_comm _ _

/-- The full punctured Laurent torus and two-root slope line are inverse presentations. -/
def slopeLaurentPunctureEquiv : L ≃ₐ[K] P :=
  AlgEquiv.ofAlgHom (laurentPunctureToSlope a) (slopeToLaurentPuncture a)
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (slopePolynomial (a : K)))
      apply Polynomial.algHom_ext
      change laurentPunctureToSlope a (slopeToLaurentPuncture a z) = z
      rw [slopeToLaurentPuncture_z, laurentPunctureToSlope_parameter])
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers r)
      apply IsLocalization.algHom_ext (Submonoid.powers (X : K[X]))
      apply Polynomial.algHom_ext
      change slopeToLaurentPuncture a
        (laurentPunctureToSlope a
          (algebraMap K[T;T⁻¹] L (algebraMap K[X] K[T;T⁻¹] X))) =
        algebraMap K[T;T⁻¹] L (algebraMap K[X] K[T;T⁻¹] X)
      rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X,
        laurentPunctureToSlope_base, slopeToLaurentPuncture_T])

/-- The algebra equivalence retains all Laurent restrictions, not only its generator. -/
theorem slopeLaurentPunctureEquiv_base (w : K[T;T⁻¹]) :
    slopeLaurentPunctureEquiv a (algebraMap K[T;T⁻¹] L w) = slopeLaurentMap a w :=
  laurentPunctureToSlope_base a w

end FLT.Mazur.WeierstrassModificationX
