/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Uniform ideal powers from mapped coefficient annihilators

Separate power bounds on generators imply radical containment in the
annihilator of the entire extended ideal. Finite generation is required only
of the ideal of denominators on the test, never of the ideal of equations.
-/

@[expose] public section
namespace FLT.Mazur.IdealMapPowerAnnihilator
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Annihilating the mapped generators annihilates their entire extended ideal. -/
theorem mem_map_annihilator_iff (g : S →+* T) (K : Ideal S) (a : T) :
    a ∈ (K.map g).annihilator ↔ ∀ z ∈ K, a * g z = 0 := by
  rw [Ideal.map, Ideal.span, Submodule.mem_annihilator_span]
  constructor
  · intro h z hz
    exact h ⟨g z, z, hz, rfl⟩
  · intro h z
    obtain ⟨w, hw, he⟩ := z.property
    change a * z.val = 0
    rw [← he]
    exact h w hw

/-- All denominator combinations lie in the radical of the full equation annihilator. -/
theorem map_le_radical_annihilator (f : R →+* T) (g : S →+* T)
    (I : Ideal R) (K : Ideal S)
    (h : ∀ a ∈ I, ∃ k : ℕ, ∀ z ∈ K, f a ^ k * g z = 0) :
    I.map f ≤ (K.map g).annihilator.radical := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  obtain ⟨k, hk⟩ := h a ha
  exact ⟨k, (mem_map_annihilator_iff g K _).mpr hk⟩

/-- A finite denominator ideal supplies one power for every coefficient and combination. -/
theorem exists_map_pow_le_annihilator (f : R →+* T) (g : S →+* T)
    (I : Ideal R) (K : Ideal S) (hfg : (I.map f).FG)
    (h : ∀ a ∈ I, ∃ k : ℕ, ∀ z ∈ K, f a ^ k * g z = 0) :
    ∃ k : ℕ, (I.map f) ^ k ≤ (K.map g).annihilator :=
  Ideal.exists_pow_le_of_le_radical_of_fg (map_le_radical_annihilator f g I K h) hfg

end FLT.Mazur.IdealMapPowerAnnihilator
