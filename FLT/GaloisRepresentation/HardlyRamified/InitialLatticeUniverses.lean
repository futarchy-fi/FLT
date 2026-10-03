/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.LatticeTransferUniverses
public import FLT.GaloisRepresentation.HardlyRamified.CoordinateChange

/-! # The original integral lattice in arbitrary universes -/

@[expose] public noncomputable section
open Module IsLocalRing GaloisRepresentation TensorProduct
open scoped TensorProduct NumberField ThreeAdicPlan
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan

/-- The image of an integral representation in its generic fibre is a stable
lattice, canonically isomorphic to the integral representation. -/
theorem exists_initial_stable_lattice_universes
    {O K V : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [TopologicalSpace O] [IsTopologicalRing O]
    [TopologicalSpace K] [IsTopologicalRing K] [ContinuousSMul O K]
    [AddCommGroup V] [Module O V] [Module.Finite O V] [Module.Free O V]
    (ρ : GaloisRep ℚ O V) (hOK : Topology.IsInducing (algebraMap O K)) :
    ∃ (Λ : Submodule O (K ⊗[O] V))
      (hΛ : StableLattice.IsStableLattice (ρ.baseChange K).toRepresentation Λ)
      (e : V ≃ₗ[O] Λ), ρ.conj e = latticeGaloisRep (ρ.baseChange K) Λ hΛ hOK := by
  classical
  let j : V →ₗ[O] K ⊗[O] V := TensorProduct.mk O K V 1
  let Λ := LinearMap.range j
  have hj : Function.Injective j := Module.Flat.tensorProduct_mk_injective O V K
  have hlat : Submodule.IsLattice K Λ := by
    constructor
    · simpa only [Submodule.map_top] using Module.Finite.fg_top.map j
    · apply top_unique
      intro x hx
      clear hx
      induction x using TensorProduct.inductionOn with
      | tmul a x =>
        have hx : j x ∈ Submodule.span K (Λ : Set (K ⊗[O] V)) :=
          Submodule.subset_span (LinearMap.mem_range_self j x)
        have hs := (Submodule.span K (Λ : Set (K ⊗[O] V))).smul_mem a hx
        change a • ((1 : K) ⊗ₜ[O] x) ∈ _ at hs
        simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hs
      | add x y hx hy => exact Submodule.add_mem _ hx hy
  have hstable : StableLattice.Stabilizes (ρ.baseChange K).toRepresentation Λ := by
    intro g
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨ρ g z, rfl⟩
    · rintro ⟨z, rfl⟩
      refine ⟨j (ρ g⁻¹ z), LinearMap.mem_range_self j _, ?_⟩
      change (1 : K) ⊗ₜ[O] (ρ g (ρ g⁻¹ z)) = (1 : K) ⊗ₜ[O] z
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  let hΛ : StableLattice.IsStableLattice (ρ.baseChange K).toRepresentation Λ :=
    ⟨hlat, hstable⟩
  let e : V ≃ₗ[O] Λ := LinearEquiv.ofInjective j hj
  refine ⟨Λ, hΛ, e, ?_⟩
  ext g x
  change j (ρ g (e.symm x)) = (ρ.baseChange K) g (x : K ⊗[O] V)
  have hx : j (e.symm x) = (x : K ⊗[O] V) :=
    congrArg Subtype.val (e.apply_symm_apply x)
  rw [← hx]
  rfl

/-- An integral hardly-ramified model gives hardly-ramified representations on
all stable lattices of its generic fibre. -/
theorem hardlyRamified_of_integral_lattice_universes {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {O K V : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Field K] [Algebra O K] [IsFractionRing O K]
    [TopologicalSpace O] [IsTopologicalRing O]
    [TopologicalSpace K] [IsTopologicalRing K] [ContinuousSMul O K]
    [AddCommGroup V] [Module O V] [Module.Finite O V] [Module.Free O V]
    (hV : Module.rank O V = 2) {ρ : GaloisRep ℚ O V}
    (hρ : IsHardlyRamified hp hV ρ)
    (Λ : Submodule O (K ⊗[O] V))
    (hΛ : StableLattice.IsStableLattice (ρ.baseChange K).toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hΛdim : Module.rank O Λ = 2) :
    let := hΛ.isLattice
    IsHardlyRamified hp hΛdim (latticeGaloisRep (ρ.baseChange K) Λ hΛ hOK) := by
  obtain ⟨Λ₀, h₀, e, he⟩ := exists_initial_stable_lattice_universes ρ hOK
  let := h₀.isLattice
  have h₀dim : Module.rank O Λ₀ = 2 := by
    rw [Module.rank_eq_ofNat_iff_finrank_eq_ofNat 2, ← e.finrank_eq]
    exact Module.finrank_eq_of_rank_eq hV
  have h₀HR := hρ.conj hp hV h₀dim e
  rw [he] at h₀HR
  exact hardlyRamified_lattice_transfer_universes hp (ρ.baseChange K) Λ₀ Λ h₀ hΛ hOK
    h₀dim hΛdim h₀HR

end ThreeAdicPlan
