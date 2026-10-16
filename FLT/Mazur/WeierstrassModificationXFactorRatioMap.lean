/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFactorGapUnits
public import FLT.Mazur.WeierstrassModificationXInitialMobiusEquiv

/-!
# Full factor-ratio coordinates on the original arithmetic initial chart

The corrected coordinates are a⁻² t U² and V/U. They preserve the complete
normalized smoothing and use the actual factors, so reflection of the second
coordinate becomes exactly reciprocal wherever both factors are invertible.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s τ : R) (hτ : s = W.a₁ ^ 2 * τ)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (g : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (hu : IsUnit (g (polynomialOppositeFactor W s b3 b4 b6 r)))
local notation "U" => g (polynomialOppositeFactor W s b3 b4 b6 r)
local notation "V" => g (polynomialSmallFactor W s b3 b4 b6 r)
local notation "a" => zeroInitialTangentUnit W ha
local notation "ai" => algebraMap R S (↑a⁻¹ : R)

/-- The full original factor ratio is defined even where its small factor vanishes. -/
def initialFactorRatio : S := V * ↑hu.unit⁻¹

/-- The first coordinate retains the square of the entire original opposite factor. -/
def initialFactorRatioFirst : S := ai ^ 2 * g (t W s b3 b4 b6) * U ^ 2

/-- The corrected ratio has the actual original opposite-factor denominator. -/
theorem initialFactorRatio_denominator :
    initialFactorRatio W s b3 b4 b6 r g hu * U = V := by
  rw [initialFactorRatio, mul_assoc, hu.val_inv_mul, mul_one]

include hr hτ in
/-- The full corrected coordinates have exactly the normalized nonzero smoothing product. -/
theorem initialFactorRatio_relation :
    initialFactorRatioFirst W ha s b3 b4 b6 r g *
      initialFactorRatio W s b3 b4 b6 r g hu = algebraMap R S τ := by
  have h := congrArg g (polynomialFactors_incidence W s b3 b4 b6 r hr)
  simp only [map_mul, AlgHom.commutes] at h
  have hi : ai * algebraMap R S W.a₁ = 1 := by
    rw [← map_mul, show (↑a⁻¹ : R) * W.a₁ = 1 from (a).inv_mul, map_one]
  have ht : algebraMap R S s = (algebraMap R S W.a₁) ^ 2 * algebraMap R S τ := by
    rw [hτ, map_mul, map_pow]
  have hd := initialFactorRatio_denominator W s b3 b4 b6 r g hu
  change (ai ^ 2 * g (t W s b3 b4 b6) * U ^ 2) * _ = _
  calc
    _ = ai ^ 2 * g (t W s b3 b4 b6) * U *
        (initialFactorRatio W s b3 b4 b6 r g hu * U) := by ring
    _ = ai ^ 2 * (g (t W s b3 b4 b6) * (V * U)) := by rw [hd]; ring
    _ = ai ^ 2 * (algebraMap R S W.a₁) ^ 2 * algebraMap R S τ := by rw [h, ht]; ring
    _ = (ai * algebraMap R S W.a₁) ^ 2 * algebraMap R S τ := by ring
    _ = algebraMap R S τ := by rw [hi, one_pow, one_mul]

variable (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)

include ha hI hrI h3 in
/-- The exact factor ratio avoids one on the whole original initial neighborhood. -/
theorem initialFactorRatio_sub_one_isUnit :
    IsUnit (initialFactorRatio W s b3 b4 b6 r g hu - 1) := by
  have he : initialFactorRatio W s b3 b4 b6 r g hu - 1 =
      -(U - V) * ↑hu.unit⁻¹ := by
    dsimp only [initialFactorRatio]
    linear_combination hu.mul_val_inv
  rw [he]
  exact (evaluatedFactorGap_isUnit W s b3 b4 b6 r I hrI h3 g hI ha).neg.mul (Units.isUnit _)

/-- The complete corrected normalized node evaluation, before localization. -/
def initialFactorRatioBase : NodalFiber.Coordinate τ →ₐ[R] S :=
  NodalFiber.evaluation τ (initialFactorRatioFirst W ha s b3 b4 b6 r g)
    (initialFactorRatio W s b3 b4 b6 r g hu)
    (initialFactorRatio_relation W ha s τ hτ b3 b4 b6 r hr g hu)

/-- All functions of the full fractional polygon neighborhood pull back by the actual factors. -/
def initialFactorRatioMap : NodalFiber.TangentOpen τ (-1 : R) →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom
    (NodalFiber.q τ + algebraMap R (NodalFiber.Coordinate τ) (-1 : R))
    (f := initialFactorRatioBase W ha s τ hτ b3 b4 b6 r hr g hu) (by
      simp only [initialFactorRatioBase, map_neg, map_one, ← sub_eq_add_neg,
        map_sub, NodalFiber.evaluation_q]
      exact initialFactorRatio_sub_one_isUnit W ha s b3 b4 b6 r g hu I hI hrI h3)

/-- The whole corrected map preserves the explicit normalized node evaluation. -/
theorem initialFactorRatioMap_base (z : NodalFiber.Coordinate τ) :
    initialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr g hu I hI hrI h3
      (algebraMap _ (NodalFiber.TangentOpen τ (-1 : R)) z) =
        initialFactorRatioBase W ha s τ hτ b3 b4 b6 r hr g hu z := by
  rw [initialFactorRatioMap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

end FLT.Mazur.WeierstrassModificationX
