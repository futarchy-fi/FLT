/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalRelationClosure

/-!
# Principal coefficient maps with prescribed denominators

An equality of denominators constructs the localization map without changing
the target type. Fractions whose numerators descend then descend through it.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.NoetherianRelationContraction

variable {A B : Type*} [CommRing A] [CommRing B]
  (c : A →+* B) (r : A) (s : B) (h : c r = s)

/-- The coefficient map with an explicitly prescribed target denominator. -/
def principalTransport : Localization.Away r →+* Localization.Away s :=
  IsLocalization.map (M := Submonoid.powers r) (T := Submonoid.powers s) _ c (by
    rw [← h, ← Submonoid.map_powers]
    exact (Submonoid.powers r).le_comap_map)

/-- The transported map commutes with the two localization maps. -/
theorem principalTransport_comp :
    (principalTransport c r s h).comp (algebraMap A (Localization.Away r)) =
      (algebraMap B (Localization.Away s)).comp c := by
  exact IsLocalization.map_comp _

/-- Prescribing the target denominator retains injectivity. -/
theorem principalTransport_injective (hc : Function.Injective c) :
    Function.Injective (principalTransport c r s h) := by
  let _ : IsLocalization ((Submonoid.powers r).map c) (Localization.Away s) := by
    rw [Submonoid.map_powers, h]
    infer_instance
  exact IsLocalization.map_injective_of_injective (Submonoid.powers r)
    (Localization.Away r) (Localization.Away s) hc

/-- A fraction descends whenever its numerator does; its denominator is a power of `s`. -/
theorem principalTransport_mk'_mem_range (p : B) (m : Submonoid.powers s)
    (hp : p ∈ Set.range c) :
    IsLocalization.mk' (Localization.Away s) p m ∈
      Set.range (principalTransport c r s h) := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨k, hk⟩ := m.property
  refine ⟨IsLocalization.mk' (M := Submonoid.powers r)
    (Localization.Away r) a ⟨r ^ k, ⟨k, rfl⟩⟩, ?_⟩
  unfold principalTransport
  rw [IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  change c (r ^ k) = m.val
  rw [map_pow, h]
  exact hk

end FLT.Mazur.NoetherianRelationContraction
