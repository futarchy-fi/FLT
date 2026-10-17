/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageRestrictionLE
public import FLT.Mazur.NilpotentAlgebraHigherOrderError

/-!
# Full Laurent coefficient squares across arbitrary arithmetic stages

Adjacent squares propagate to every earlier stage. An identity at stage k
therefore detects the exact pi^(k+1) divisibility of every error coefficient
at every later stage, with no support restriction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open LaurentPolynomial PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R}
variable (a : (m : ℕ) → (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (ha : ∀ m, (coeffMap (restriction R π m).toRingHom).comp (a (m + 1)).toRingHom =
    (a m).toRingHom.comp (coeffMap (restriction R π m).toRingHom))

include ha

/-- Every nonconsecutive square follows from the original adjacent full coefficient squares. -/
theorem laurentSystem_restrictionLE {k m : ℕ} (h : k ≤ m) :
    (coeffMap (restrictionLE R π h).toRingHom).comp (a m).toRingHom =
      (a k).toRingHom.comp (coeffMap (restrictionLE R π h).toRingHom) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [restrictionLE_refl]
    change (coeffMap (RingHom.id (Quotient R π k))).comp (a k).toRingHom =
      (a k).toRingHom.comp (coeffMap (RingHom.id (Quotient R π k)))
    rw [coeffMap_id]
    rfl
  | succ m h ih =>
    rw [restrictionLE_succ R π h]
    change (coeffMap ((restrictionLE R π h).toRingHom.comp
      (restriction R π m).toRingHom)).comp (a (m + 1)).toRingHom =
      (a k).toRingHom.comp (coeffMap ((restrictionLE R π h).toRingHom.comp
        (restriction R π m).toRingHom))
    rw [coeffMap_comp]
    apply RingHom.ext
    intro z
    exact (congrArg (coeffMap (restrictionLE R π h).toRingHom)
      (DFunLike.congr_fun (ha m) z)).trans
        (DFunLike.congr_fun ih (coeffMap (restriction R π m).toRingHom z))

/-- The full error vanishes after restriction to any layer on which the map is identity. -/
theorem laurentSystem_error_restriction {k m : ℕ} (h : k ≤ m)
    (hk : a k = AlgHom.id (Quotient R π k) _) (z : (Quotient R π m)[T;T⁻¹]) :
    coeffMap (restrictionLE R π h).toRingHom (a m z - z) = 0 := by
  rw [map_sub]
  have he := DFunLike.congr_fun (laurentSystem_restrictionLE a ha h) z
  rw [hk] at he
  exact sub_eq_zero.mpr he

/-- Vanishing at the earlier layer detects every coefficient of the full error. -/
theorem laurentSystem_error_coeff_dvd {k m : ℕ} (h : k ≤ m)
    (hk : a k = AlgHom.id (Quotient R π k) _) (z : (Quotient R π m)[T;T⁻¹]) (d : ℤ) :
    parameter R π m ^ (k + 1) ∣ (a m z - z).coeff d :=
  restrictionLE_coeff_dvd R π h _ (laurentSystem_error_restriction a ha h hk z) d

/-- All coefficients assemble into divisibility of the actual complete Laurent error. -/
theorem laurentSystem_error_dvd {k m : ℕ} (h : k ≤ m)
    (hk : a k = AlgHom.id (Quotient R π k) _) (z : (Quotient R π m)[T;T⁻¹]) :
    C (parameter R π m ^ (k + 1)) ∣ a m z - z :=
  restrictionLE_laurent_dvd R π h _ (laurentSystem_error_restriction a ha h hk z)

/-- The full error belongs to the exact extended coefficient-ideal power. -/
theorem laurentSystem_error_sub_mem {k m : ℕ} (h : k ≤ m)
    (hk : a k = AlgHom.id (Quotient R π k) _) (z : (Quotient R π m)[T;T⁻¹]) :
    a m z - z ∈ ((ideal (Quotient R π m) (parameter R π m)).map
      (algebraMap (Quotient R π m) (Quotient R π m)[T;T⁻¹])) ^ (k + 1) := by
  change a m z - z ∈ ((Ideal.span {parameter R π m}).map
    (algebraMap (Quotient R π m) (Quotient R π m)[T;T⁻¹])) ^ (k + 1)
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← map_pow]
  exact laurentSystem_error_dvd a ha h hk z

/-- An identity at stage k raises the full coefficient filtration by k+1. -/
theorem laurentSystem_error_mem_power {k m : ℕ} (h : k ≤ m)
    (hk : a k = AlgHom.id (Quotient R π k) _) (r : ℕ) (z : (Quotient R π m)[T;T⁻¹])
    (hz : z ∈ ((ideal (Quotient R π m) (parameter R π m)).map
      (algebraMap (Quotient R π m) (Quotient R π m)[T;T⁻¹])) ^ r) :
    a m z - z ∈ ((ideal (Quotient R π m) (parameter R π m)).map
      (algebraMap (Quotient R π m) (Quotient R π m)[T;T⁻¹])) ^ (r + (k + 1)) :=
  NilpotentAlgebraHigherOrderError.error_mem_power _ _ _
    (laurentSystem_error_sub_mem a ha h hk) r z hz

end FLT.Mazur.PolygonArithmeticStages
