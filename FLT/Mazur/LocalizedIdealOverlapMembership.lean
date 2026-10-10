/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Clearing ideal membership on a principal overlap

An inclusion of extended ideals on a genuine principal overlap yields the
denominator-power condition needed to patch ambient numerators. The overlap
ring is a localization, not an assumed relation between finite-stage kernels.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalIdealPatching

universe u v w z

variable {P : Type u} {S : Type v} {T : Type w} {U : Type z}
  [CommRing P] [CommRing S] [CommRing T] [CommRing U] [Algebra T U]

/-- Ideal membership on an actual overlap clears by a power of its denominator. -/
theorem exists_pow_mul_mem_of_overlap (r x : P) (φ : P →+* S) (ψ : P →+* T)
    [IsLocalization.Away (ψ r) U] (f : S →+* U)
    (hcomm : f.comp φ = (algebraMap T U).comp ψ) (J : Ideal S) (K : Ideal T)
    (hJK : J.map f ≤ K.map (algebraMap T U)) (hx : φ x ∈ J) :
    ∃ n : ℕ, ψ (r ^ n * x) ∈ K := by
  have hm : algebraMap T U (ψ x) ∈ K.map (algebraMap T U) := by
    rw [← RingHom.comp_apply, ← hcomm, RingHom.comp_apply]
    exact hJK (Ideal.mem_map_of_mem f hx)
  obtain ⟨m, hm, hx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (ψ r)) U K (ψ x)).mp hm
  obtain ⟨n, rfl⟩ := hm
  exact ⟨n, by simpa only [map_mul, map_pow] using hx⟩

end FLT.Mazur.PrincipalIdealPatching
