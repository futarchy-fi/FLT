/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteAlgebraPointComponent
public import FLT.Mathlib.RingTheory.LocalizedPresentation

/-! # Component projection preserves the original localized presentation kernel -/

@[expose] public noncomputable section

namespace FiniteAlgebra
attribute [local instance] RingHom.ker_isPrime

variable {k S A : Type*} [Field k] [CommRing S] [CommRing A]
  [Algebra k S] [Algebra k A] [IsArtinianRing A]

/-- At a pointed component, the original presentation and the projected presentation
have exactly the same localized ideal. The comparison retains the original source. -/
theorem map_ker_eq_component_localized (ε : A →ₐ[k] k)
    (f : S →ₐ[k] A) (hf : Function.Surjective f) :
    (RingHom.ker f).map (algebraMap S
      (Localization.AtPrime (RingHom.ker (ε.comp f)))) =
    (RingHom.ker ((pointProjection ε).comp f)).map (algebraMap S
      (Localization.AtPrime (RingHom.ker (ε.comp f)))) := by
  let P := RingHom.ker (ε.comp f)
  let L := Localization.AtPrime P
  apply le_antisymm
  · apply Ideal.map_mono
    intro s hs
    change pointProjection ε (f s) = 0
    rw [show f s = 0 from hs, map_zero]
  · apply Ideal.map_le_iff_le_comap.mpr
    intro s hs
    obtain ⟨t, ht⟩ := hf (componentIdempotent A (pointComponentIndex ε))
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl L _ s).mpr
    refine ⟨t, ?_, ?_⟩
    · change ε (f t) ≠ 0
      rw [ht, point_componentIdempotent]
      exact one_ne_zero
    · change f (t * s) = 0
      rw [map_mul, ht]
      have hmem : f s ∈ pointComponentIdeal ε := Ideal.Quotient.eq_zero_iff_mem.mp hs
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
      rw [hb, ← mul_assoc,
        (componentIdempotent_isIdempotent A (pointComponentIndex ε)).mul_one_sub_self, zero_mul]

end FiniteAlgebra
