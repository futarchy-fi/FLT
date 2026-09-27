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
Ribet's lemma then rules out irreducibility if every stable lattice has such a quotient.
-/

@[expose] public section

namespace StableLattice

/-- In dimension two, a trivial quotient and the determinant identify both
characters of the extension. The residual arithmetic input is the functional itself. -/
theorem isExtensionOf_of_trivial_quotient
    {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V)
    (hdim : Module.finrank k V = 2) (χ : G →* kˣ)
    (hdet : ∀ g, LinearMap.det (ρ g) = (χ g : k))
    (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hπG : ∀ g v, π (ρ g v) = π v) :
    IsExtensionOf ρ χ 1 := by
  let e := π.quotKerEquivOfSurjective hπ
  have hq : Module.finrank k (V ⧸ LinearMap.ker π) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  have hk : Module.finrank k (LinearMap.ker π) = 1 := by
    have h := (LinearMap.ker π).finrank_quotient_add_finrank
    rw [hq, hdim] at h
    omega
  have hstable (g : G) : LinearMap.ker π ≤ (LinearMap.ker π).comap (ρ g) := by
    intro v hv
    simpa only [Submodule.mem_comap, LinearMap.mem_ker, hπG] using hv
  obtain ⟨ψ, hψ⟩ := exists_character_of_stable_line ρ hk (fun g ↦ by
    rintro _ ⟨v, hv, rfl⟩
    exact hstable g hv)
  have hcharacters (g : G) : (ψ g : k) = (χ g : k) := by
    have hres : (ρ g).restrict (hstable g) =
        (ψ g : k) • (LinearMap.id : LinearMap.ker π →ₗ[k] LinearMap.ker π) := by
      ext v
      exact hψ g v v.property
    have hquot : (LinearMap.ker π).mapQ (LinearMap.ker π) (ρ g) (hstable g) =
        LinearMap.id := by
      ext v
      change (Submodule.Quotient.mk (ρ g v) : V ⧸ LinearMap.ker π) =
        Submodule.Quotient.mk v
      rw [Submodule.Quotient.eq]
      simp [LinearMap.mem_ker, hπG]
    have hd := (ρ g).det_eq_det_mul_det (LinearMap.ker π) (hstable g)
    rw [hres, hquot, LinearMap.det_smul, hk, pow_one,
      LinearMap.det_id, LinearMap.det_id, mul_one, mul_one] at hd
    exact hd.symm.trans (hdet g)
  refine ⟨LinearMap.ker π, hk, ?_, ?_⟩
  · intro g v hv
    rw [hψ g v hv, hcharacters g]
  · intro g v
    simp [LinearMap.mem_ker, hπG]


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

open IsLocalRing

/-- If every stable lattice has a trivial residual quotient, Ribet's lemma
rules out irreducibility when the residual characters are `1` and a nontrivial `χ`. -/
@[nolint unusedArguments]
theorem not_isIrreducible_of_all_lattices_trivial_quotient
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    {W : Type*} [AddCommGroup W] [Module K W] [Module O W]
    [IsScalarTower O K W] [FiniteDimensional K W]
    {G : Type*} [Group G]
    [IsAdicComplete (maximalIdeal O) O]
    (ρ : Representation K G W) (hdim : Module.finrank K W = 2)
    (Λ₀ : Submodule O W) (h₀ : IsStableLattice ρ Λ₀)
    (χ : G →* (ResidueField O)ˣ) (hne : ∃ g, χ g ≠ 1)
    (hss : HasSemisimplification (reducedRep ρ Λ₀ h₀.stable) 1 χ)
    (hQ : ∀ (Λ : Submodule O W) (h : IsStableLattice ρ Λ),
      ∃ π : Reduction O W Λ →ₗ[ResidueField O] ResidueField O,
        Function.Surjective π ∧
          ∀ g v, π (reducedRep ρ Λ h.stable g v) = π v) :
    ¬ ρ.IsIrreducible := by
  intro hirr
  let : ρ.IsIrreducible := hirr
  obtain ⟨Λ, h, hext, hns⟩ := ribet_lemma_proof ρ hdim Λ₀ h₀ 1 χ hss
  obtain ⟨π, hπ, hπG⟩ := hQ Λ h
  exact hns (isSplitExtensionOf_of_trivial_quotient
    (reducedRep ρ Λ h.stable) χ hext hne π hπ hπG)

end StableLattice
