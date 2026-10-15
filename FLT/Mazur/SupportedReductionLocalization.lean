/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Localization of reductions with coordinate-supported kernels

Uniform annihilation by coordinate powers gives uniform annihilation by
a power of their sum. A surjective reduction then becomes an isomorphism
on that principal open. If the reduced sum is regular, the localization
kernel is exactly the original reduction kernel.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SupportedReductionLocalization
variable {A N : Type*} [CommRing A] [CommRing N]

/-- Powers annihilating an ideal separately also give one annihilating power of their sum. -/
theorem sum_power (J : Ideal A) (x y : A) (m n : ℕ)
    (hx : ∀ z ∈ J, x ^ m * z = 0) (hy : ∀ z ∈ J, y ^ n * z = 0) :
    ∃ k : ℕ, ∀ z ∈ J, (x + y) ^ k * z = 0 := by
  let I := Module.annihilator A J
  have ha : x ∈ I.radical := by
    refine ⟨m, Module.mem_annihilator.mpr ?_⟩
    intro z
    apply Subtype.ext
    exact hx z.val z.property
  have hb : y ∈ I.radical := by
    refine ⟨n, Module.mem_annihilator.mpr ?_⟩
    intro z
    apply Subtype.ext
    exact hy z.val z.property
  obtain ⟨k, hk⟩ := I.radical.add_mem ha hb
  refine ⟨k, fun z hz ↦ ?_⟩
  exact congrArg Subtype.val (Module.mem_annihilator.mp hk ⟨z, hz⟩)

/-- A surjection with a power-annihilated kernel is an isomorphism after localization. -/
theorem awayMap_bijective (r : A →+* N) (hr : Function.Surjective r) (a : A)
    (ha : ∃ k : ℕ, ∀ z ∈ RingHom.ker r, a ^ k * z = 0) :
    Function.Bijective (Localization.awayMap r a) := by
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    obtain ⟨k, hk⟩ := ha
    exact fun z hz ↦ ⟨k, hk z hz⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro z
    obtain ⟨w, hw⟩ := hr z
    exact ⟨w, 0, by simpa only [pow_zero, one_mul] using hw⟩

/-- The canonical isomorphism retains the actual reduction map on the principal open. -/
def awayEquiv (r : A →+* N) (hr : Function.Surjective r) (a : A)
    (ha : ∃ k : ℕ, ∀ z ∈ RingHom.ker r, a ^ k * z = 0) :
    Localization.Away a ≃+* Localization.Away (r a) :=
  RingEquiv.ofBijective (Localization.awayMap r a) (awayMap_bijective r hr a ha)

/-- When the target coordinate is regular, exactly the reduction kernel dies on the open. -/
theorem localization_ker (r : A →+* N) (a : A)
    (ha : ∃ k : ℕ, ∀ z ∈ RingHom.ker r, a ^ k * z = 0)
    (hr : IsRegular (r a)) :
    RingHom.ker (algebraMap A (Localization.Away a)) = RingHom.ker r := by
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a)
      (Localization.Away a) z).mp hz
    obtain ⟨k, hk⟩ := c.property
    change a ^ k = c.val at hk
    have he : a ^ k * z = 0 := by rw [hk]; exact hc
    have hf := congrArg r he
    rw [map_mul, map_pow, map_zero] at hf
    exact (hr.pow k).left (hf.trans (mul_zero _).symm)
  · intro hz
    obtain ⟨k, hk⟩ := ha
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers a)
      (Localization.Away a) z).mpr ⟨⟨a ^ k, ⟨k, rfl⟩⟩, hk z hz⟩

end FLT.Mazur.SupportedReductionLocalization
