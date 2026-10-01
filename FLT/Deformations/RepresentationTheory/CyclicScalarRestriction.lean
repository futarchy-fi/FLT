/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.StableLinePair
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Scalar restriction and a cyclic quotient

An eigenline for a lift of a quotient generator is stable under the entire
group when the normal subgroup acts by scalars. Thus a two-dimensional
representation over an algebraically closed field cannot be irreducible.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V) (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)]

/-- Scalar action of a normal subgroup with cyclic quotient forces
reducibility in dimension two. The quotient need not be finite. -/
theorem not_isIrreducible_of_scalar_restriction
    (hV : Module.finrank k V = 2)
    (hscalar : ∀ h : H, ∃ a : k, ρ h = a • LinearMap.id) :
    ¬ ρ.IsIrreducible := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank k V)
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := G ⧸ H)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (ρ g)
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  let L : Submodule k V := Submodule.span k {v}
  have hL : Module.finrank k L = 1 := finrank_span_singleton hv.2
  have map_eq (t : G) (ht : L.map (ρ t) ≤ L) : L.map (ρ t) = L := by
    apply Submodule.eq_of_le_of_finrank_le ht
    exact le_of_eq (LinearEquiv.finrank_map_eq
      (LinearEquiv.ofBijective (ρ t) (ρ.apply_bijective t)) L).symm
  let S : Subgroup G :=
    { carrier := {t | L.map (ρ t) = L}
      one_mem' := by simp [Module.End.one_eq_id]
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hy, hx]
      inv_mem' := by
        intro t ht
        change L.map (ρ t⁻¹) = L
        apply Submodule.map_injective_of_injective (ρ.apply_bijective t).1
        rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
          mul_inv_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]
        exact ht.symm }
  have hg : g ∈ S := by
    apply map_eq
    rintro w ⟨u, hu, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, hv.apply_eq_smul, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  have hH : H ≤ S := by
    intro h hh
    apply map_eq
    obtain ⟨b, hb⟩ := hscalar ⟨h, hh⟩
    rintro w ⟨u, hu, rfl⟩
    simpa [hb] using L.smul_mem b hu
  have hall (t : G) : t ∈ S := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hq (QuotientGroup.mk' H t))
    have hmem : (g ^ n)⁻¹ * t ∈ H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' H ((g ^ n)⁻¹ * t) = 1
      rw [map_mul, map_inv, map_zpow, hn, inv_mul_cancel]
    have hm := S.mul_mem (S.zpow_mem hg n) (hH hmem)
    simpa using hm
  intro hirr
  obtain ⟨t, ht⟩ := ρ.exists_map_line_ne hV hirr hL
  exact ht (hall t)

end Representation
