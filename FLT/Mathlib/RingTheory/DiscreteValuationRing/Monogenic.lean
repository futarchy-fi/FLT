/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Monogenic finite extensions of discrete valuation rings

A finite subalgebra of a DVR is the whole ring if it surjects onto the residue
field and contains a uniformizer. This is the Nakayama step in constructing an
integral power basis from a separable residue-field generator.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

namespace Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain S] [IsDiscreteValuationRing S] [Module.Finite R S]

/-- A finite intermediate algebra of a local domain is local. -/
theorem isLocalRing_of_finite (C : Subalgebra R S) : IsLocalRing C := by
  have : Module.Finite C S := Module.Finite.of_restrictScalars_finite R C S
  have : IsLocalHom (algebraMap C S) := inferInstance
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (algebraMap C S a)
  exact h.imp (IsLocalHom.map_nonunit _) (fun h ↦
    isUnit_of_map_unit (algebraMap C S) _ (by simpa using h))

/-- A finite intermediate algebra containing a uniformizer and surjecting onto
the residue field is the full DVR. -/
theorem eq_top_of_residue_surjective_of_irreducible (C : Subalgebra R S)
    (hres : ∀ s : S, ∃ c : C, residue S c = residue S s)
    {π : S} (hπ : Irreducible π) (hπC : π ∈ C) : C = ⊤ := by
  let := C.isLocalRing_of_finite
  have : Module.Finite C S := Module.Finite.of_restrictScalars_finite R C S
  have : IsLocalHom (algebraMap C S) := inferInstance
  have hm : (maximalIdeal C).map (algebraMap C S) = maximalIdeal S := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, maximalIdeal_comap]
    · rw [hπ.maximalIdeal_eq, Ideal.span_le]
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      apply Ideal.mem_map_of_mem (algebraMap C S) (x := (⟨x, hπC⟩ : C))
      rw [← maximalIdeal_comap (algebraMap C S)]
      exact hπ.not_isUnit
  have htop : (⊤ : Submodule C S) ≤ (Algebra.linearMap C S).range := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)
    rw [Ideal.smul_top_eq_map, hm]
    intro s _
    obtain ⟨c, hc⟩ := hres s
    refine Submodule.mem_sup.mpr ⟨c, ⟨c, rfl⟩, s - c, ?_, by simp⟩
    change s - c ∈ maximalIdeal S
    rw [← residue_eq_zero_iff, map_sub, hc, sub_self]
  apply top_unique
  intro s _
  obtain ⟨c, hc⟩ := htop (Submodule.mem_top : s ∈ (⊤ : Submodule C S))
  exact hc ▸ c.property

end Subalgebra
