/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOne
public import FLT.Mazur.WeierstrassSlopeLaurentGeometry

/-!
# The ordered tangent parameter on the original scale-one tensor chart

The two invertible tangent factors are v-r and v-r+a. Their ratio defines
an actual Laurent map on the whole original tensor algebra, retaining the
root shift. Its comparison with the canonical slope map holds on all functions.
-/

@[expose] public noncomputable section
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0) (h6 : algebraMap R S b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => WeierstrassCurve.a₁ (rootShearCurve (W.map (algebraMap R S)) r)
local notation "P" => SlopeOpen a
local notation "A" => ScalarExtension W s b3 b4 b6 S
local notation "E" => tensorShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
/-- The original slope with its chosen tangent root subtracted. -/
def tensorShearScaleOneSlope : A := by
  let v₀ : A := (1 : S) ⊗ₜ[R] v W s b3 b4 b6
  exact v₀ - algebraMap S A r

local notation "z₀" => tensorShearScaleOneSlope W s b3 b4 b6 S r

include hs h3 h4 h6 hr

/-- Both actual unsheared tangent factors are units on the full initial tensor chart. -/
theorem tensorShearScaleOne_tangent_units :
    IsUnit z₀ ∧ IsUnit (z₀ + algebraMap S A a) := by
  have hz : E z₀ = slopeZ a := by
    rw [tensorShearScaleOneSlope, map_sub, tensorShearScaleOneEquiv_v,
      AlgEquiv.commutes, add_sub_cancel_right]
  constructor
  · apply (MulEquiv.isUnit_map E).mp
    rw [hz]
    exact (slope_units a).1
  · apply (MulEquiv.isUnit_map E).mp
    rw [map_add, hz, AlgEquiv.commutes]
    exact (slope_units a).2.1

local notation "hu" => tensorShearScaleOne_tangent_units W s b3 b4 b6 S r hs h3 h4 h6 hr

/-- The actual ordered ratio of the two original tangent functions. -/
def tensorShearScaleOneParameter : Aˣ := hu.2.unit * hu.1.unit⁻¹

/-- Multiplying the actual parameter by v-r recovers v-r+a. -/
theorem tensorShearScaleOneParameter_mul :
    (tensorShearScaleOneParameter W s b3 b4 b6 S r hs h3 h4 h6 hr : A) * z₀ =
      z₀ + algebraMap S A a := by
  change (hu.2.unit : A) * (↑((hu.1.unit)⁻¹) : A) * z₀ = _
  rw [mul_assoc, Units.inv_mul_eq_one.mpr hu.1.unit_spec, mul_one, hu.2.unit_spec]

/-- The parameter gives a map of the whole Laurent coordinate algebra. -/
def tensorShearScaleOneLaurentMap : S[T;T⁻¹] →ₐ[S] A :=
  LaurentUnitPoints.evalUnit (tensorShearScaleOneParameter W s b3 b4 b6 S r hs h3 h4 h6 hr)

/-- The positive Laurent generator is the original ordered tangent ratio. -/
theorem tensorShearScaleOneLaurentMap_T :
    tensorShearScaleOneLaurentMap W s b3 b4 b6 S r hs h3 h4 h6 hr
      (LaurentPolynomial.T 1) =
        (tensorShearScaleOneParameter W s b3 b4 b6 S r hs h3 h4 h6 hr : A) := by
  rw [tensorShearScaleOneLaurentMap, LaurentUnitPoints.evalUnit_T, zpow_one]

/-- The full original Laurent map is the canonical slope parameter after the tensor comparison. -/
theorem tensorShearScaleOneLaurentMap_comparison (b : Sˣ) (hb : (b : S) = a) :
    ((E).toAlgHom).comp (tensorShearScaleOneLaurentMap W s b3 b4 b6 S r hs h3 h4 h6 hr) =
      (hb ▸ slopeLaurentMap b) := by
  apply slopeLaurent_hom_ext
  change E (tensorShearScaleOneLaurentMap W s b3 b4 b6 S r hs h3 h4 h6 hr
    (LaurentPolynomial.T 1)) = _
  apply (slope_units a).1.mul_right_cancel
  have hz : E z₀ = slopeZ a := by
    rw [tensorShearScaleOneSlope, map_sub, tensorShearScaleOneEquiv_v,
      AlgEquiv.commutes, add_sub_cancel_right]
  have hc : ∀ (c : S) (h : (b : S) = c),
      (h ▸ slopeLaurentMap b) (LaurentPolynomial.T 1) * slopeZ c =
        slopeZ c + algebraMap S (SlopeOpen c) c := by
    intro c h
    subst c
    rw [slopeLaurentMap_T, mul_assoc,
      Units.inv_mul_eq_one.mpr (slope_units (b : S)).1.unit_spec, mul_one]
  rw [tensorShearScaleOneLaurentMap_T, ← hz, ← map_mul,
    tensorShearScaleOneParameter_mul, map_add, AlgEquiv.commutes, hz,
    hc a hb]

end FLT.Mazur.WeierstrassModificationX
