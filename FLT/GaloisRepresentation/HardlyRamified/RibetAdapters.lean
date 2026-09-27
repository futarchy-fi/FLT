/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.Ribet_Lemma.Proofs
public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicAlgebra

/-! # Trivial quotients and Ribet's lemma

An invariant surjective functional splits an extension of a nontrivial character
by the trivial character, with the prescribed character on the complement.
-/

@[expose] public section

namespace StableLattice

/-- A trivial quotient splits an extension with trivial subrepresentation and
nontrivial quotient character. -/
theorem isSplitExtensionOf_of_trivial_quotient
    {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : G →* kˣ)
    (hext : IsExtensionOf ρ 1 χ)
    (hne : ∃ g, χ g ≠ 1)
    (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hπG : ∀ g v, π (ρ g v) = π v) :
    IsSplitExtensionOf ρ 1 χ := by
  obtain ⟨L, hL, hLG, hquot⟩ := hext
  obtain ⟨l, _, hspan⟩ := finrank_eq_one_iff'.mp hL
  have hnonzero : π (l : V) ≠ 0 := by
    intro hzero
    have hvanish (v : V) (hv : v ∈ L) : π v = 0 := by
      obtain ⟨c, hc⟩ := hspan ⟨v, hv⟩
      have hcv : c • (l : V) = v := congrArg Subtype.val hc
      rw [← hcv, map_smul, hzero, smul_zero]
    obtain ⟨g, hg⟩ := hne
    obtain ⟨v, hv⟩ := hπ 1
    have hchar := hvanish _ (hquot g v)
    rw [map_sub, map_smul, hπG, hv, smul_eq_mul, mul_one] at hchar
    exact hg (Units.ext (sub_eq_zero.mp hchar).symm)
  have hinter (v : V) (hv : v ∈ L) (hker : π v = 0) : v = 0 := by
    obtain ⟨c, hc⟩ := hspan ⟨v, hv⟩
    have hcv : c • (l : V) = v := congrArg Subtype.val hc
    have hc0 : c = 0 := by
      rw [← hcv, map_smul, smul_eq_mul] at hker
      exact (mul_eq_zero.mp hker).resolve_right hnonzero
    rw [← hcv, hc0, zero_smul]
  refine ⟨L, LinearMap.ker π, hL, hLG, ?_, ?_⟩
  · intro g v hv
    apply sub_eq_zero.mp
    apply hinter _ (hquot g v)
    simp only [LinearMap.mem_ker] at hv
    simp [map_sub, map_smul, hπG, hv]
  · constructor
    · rw [disjoint_iff_inf_le]
      rintro v ⟨hv, hker⟩
      exact hinter v hv hker
    · rw [codisjoint_iff_le_sup]
      intro v _
      let c := π v * (π (l : V))⁻¹
      apply Submodule.mem_sup.mpr
      refine ⟨c • (l : V), L.smul_mem c l.property, v - c • (l : V), ?_,
        add_sub_cancel _ _⟩
      simp [LinearMap.mem_ker, c, smul_eq_mul, hnonzero]

end StableLattice
