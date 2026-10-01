/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonPinchingAlgebra

/-!
# Pinching functions on principal neighborhoods of the node

Inverting a pinched function nonzero at the node preserves the description
of descended functions as those with equal endpoint values.
-/

@[expose] public noncomputable section

open Polynomial
open FLT.Mazur.PolygonNodePresentation

namespace FLT.Mazur.OneGonLocalizedPinching

variable {K : Type*} [Field K] (s : B (R := K))

/-- Functions on the principal open of the affine normalization. -/
abbrev line := Localization.Away s.val

/-- Functions on the corresponding principal open of the pinched chart. -/
abbrev chart := Localization.Away s

/-- Restriction of pinched functions to the localized affine line. -/
def restriction : chart s →+* line s :=
  IsLocalization.Away.lift s
    (g := (algebraMap K[X] (line s)).comp (B (R := K)).val.toRingHom)
    (IsLocalization.Away.algebraMap_isUnit s.val)

/-- Restriction agrees with inclusion on polynomial numerators. -/
@[simp]
theorem restriction_algebraMap (b : B (R := K)) :
    restriction s (algebraMap (B (R := K)) (chart s) b) =
      algebraMap K[X] (line s) b.val :=
  IsLocalization.Away.lift_eq _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Localization preserves the injectivity of the pinching-algebra inclusion. -/
theorem restriction_injective : Function.Injective (restriction s) := by
  let : IsLocalization.Away ((B (R := K)).val.toRingHom s) (line s) :=
    inferInstanceAs (IsLocalization.Away s.val (line s))
  change Function.Injective (IsLocalization.Away.map (chart s) (line s)
    (B (R := K)).val.toRingHom s)
  rw [IsLocalization.Away.map_injective_iff]
  intro b hb
  refine ⟨0, ?_⟩
  have hb' : b = 0 := Subtype.ext hb
  simp [hb']

variable (hs : bEval s ≠ 0)

/-- Evaluation at the first endpoint extends across the localization. -/
def atZero : line s →+* K :=
  IsLocalization.Away.lift s.val (g := evalRingHom 0)
    (isUnit_iff_ne_zero.mpr hs)

/-- Evaluation at the second endpoint extends across the localization. -/
def atOne : line s →+* K :=
  IsLocalization.Away.lift s.val (g := evalRingHom 1)
    (isUnit_iff_ne_zero.mpr (by
      change s.val.eval 1 ≠ 0
      rw [← (mem_B _).mp s.property]
      exact hs))

@[simp]
theorem atZero_algebraMap (p : K[X]) :
    atZero s hs (algebraMap K[X] (line s) p) = p.eval 0 :=
  IsLocalization.Away.lift_eq _ _ _

@[simp]
theorem atOne_algebraMap (p : K[X]) :
    atOne s hs (algebraMap K[X] (line s) p) = p.eval 1 :=
  IsLocalization.Away.lift_eq _ _ _

/-- Descended functions have equal endpoint values after localization. -/
theorem endpoint_agreement :
    (atZero s hs).comp (restriction s) = (atOne s hs).comp (restriction s) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  apply RingHom.ext
  intro b
  simp only [RingHom.comp_apply, restriction_algebraMap,
    atZero_algebraMap, atOne_algebraMap]
  exact (mem_B _).mp b.property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every localized function with equal endpoint values descends. -/
theorem range_restriction :
    (restriction s).range = RingHom.eqLocus (atZero s hs) (atOne s hs) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact RingHom.congr_fun (endpoint_agreement s hs) w
  · intro hz
    change atZero s hs z = atOne s hs z at hz
    obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj s.val z
    have h0 := congrArg (atZero s hs) hp
    have h1 := congrArg (atOne s hs) hp
    simp only [map_mul, map_pow, atZero_algebraMap, atOne_algebraMap] at h0 h1
    have hb : p ∈ B (R := K) := by
      rw [mem_B]
      rw [← h0, ← h1, hz, (mem_B _).mp s.property]
    let b : B (R := K) := ⟨p, hb⟩
    let w := algebraMap (B (R := K)) (chart s) b *
      (IsLocalization.Away.invSelf s : chart s) ^ n
    have hi : restriction s (IsLocalization.Away.invSelf s) *
        algebraMap K[X] (line s) s.val = 1 := by
      rw [mul_comm, ← restriction_algebraMap s s, ← map_mul]
      simp
    have hw : restriction s w * (algebraMap K[X] (line s) s.val) ^ n =
        algebraMap K[X] (line s) p := by
      simp only [w, map_mul, map_pow, restriction_algebraMap]
      rw [mul_assoc, ← mul_pow, hi, one_pow, mul_one]
    refine ⟨w, ?_⟩
    exact ((IsLocalization.Away.algebraMap_isUnit s.val (S := line s)).pow n).mul_right_cancel
      (hw.trans hp.symm)

end FLT.Mazur.OneGonLocalizedPinching
