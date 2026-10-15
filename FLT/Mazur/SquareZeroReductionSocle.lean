/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NilpotentIdealSocle
public import FLT.Mazur.SquareZeroReductionKernel

/-!
# Node socles detect square-zero extensions

For a square-zero reduction whose kernel is killed by powers of two
coordinates, the simultaneous annihilator detects the full extension.
If the sum is regular after reduction, its regularity before reduction
is equivalent to vanishing of the kernel.
-/

@[expose] public section
namespace FLT.Mazur.SquareZeroReductionSocle
open NilpotentIdealSocle
variable {A N : Type*} [CommRing A] [CommRing N] [IsReduced N]
  (r : A →+* N) (hsq : ∀ z, r z = 0 → z * z = 0)

include hsq in
/-- A square-zero reduction has trivial kernel exactly when its source is reduced. -/
theorem reduced_iff_ker_eq_bot : IsReduced A ↔ RingHom.ker r = ⊥ := by
  constructor
  · intro hr
    let _ := hr
    apply le_antisymm _ bot_le
    intro z hz
    exact (show IsNilpotent z from ⟨2, (pow_two z).trans (hsq z hz)⟩).eq_zero
  · intro hk
    exact isReduced_of_injective r ((RingHom.injective_iff_ker_eq_bot r).mpr hk)

include hsq in
/-- Uniform coordinate bounds reduce reducedness to the simultaneous annihilator. -/
theorem reduced_iff_socle_eq_bot (x y : A) (m n : ℕ)
    (hx : ∀ z ∈ RingHom.ker r, x ^ m * z = 0)
    (hy : ∀ z ∈ RingHom.ker r, y ^ n * z = 0) :
    IsReduced A ↔ socle (RingHom.ker r) x y = ⊥ := by
  rw [socle_eq_bot_iff _ _ _ m n hx hy, reduced_iff_ker_eq_bot r hsq]

omit [IsReduced N] in
/-- Regularity of the reduced coordinate sum places every node socle element in the kernel. -/
theorem socle_eq_full (x y : A) (hr : IsRegular (r (x + y))) :
    socle (RingHom.ker r) x y = socle ⊤ x y := by
  apply le_antisymm
  · intro z hz
    exact ⟨⟨Submodule.mem_top, hz.1.2⟩, hz.2⟩
  · intro z hz
    refine ⟨⟨?_, hz.1.2⟩, hz.2⟩
    have he : (x + y) * z = 0 := by rw [add_mul, hz.1.2, hz.2, add_zero]
    have hf := congrArg r he
    rw [map_mul, map_zero] at hf
    exact hr.left (hf.trans (mul_zero _).symm)

include hsq in
/-- Regularity of the original coordinate sum is the exact square-zero extension test. -/
theorem reduced_iff_sum_regular (x y : A) (m n : ℕ)
    (hx : ∀ z ∈ RingHom.ker r, x ^ m * z = 0)
    (hy : ∀ z ∈ RingHom.ker r, y ^ n * z = 0)
    (hr : IsRegular (r (x + y))) : IsReduced A ↔ IsRegular (x + y) := by
  constructor
  · intro ha
    have hi := (RingHom.injective_iff_ker_eq_bot r).mpr
      ((reduced_iff_ker_eq_bot r hsq).mp ha)
    apply (Commute.isRegular_iff (fun b ↦ mul_comm _ b)).mpr
    intro a b hab
    apply hi
    apply hr.left
    simpa only [← map_mul] using congrArg r hab
  · intro hs
    apply (reduced_iff_socle_eq_bot r hsq x y m n hx hy).mpr
    apply le_antisymm _ bot_le
    intro z hz
    apply hs.left
    change (x + y) * z = (x + y) * 0
    rw [add_mul, hz.1.2, hz.2, add_zero, mul_zero]

end FLT.Mazur.SquareZeroReductionSocle
