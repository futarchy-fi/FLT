/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.LatticeFlatUniverses
public import FLT.Slop.Ribet_Lemma.LatticeTameTwo
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Hardly ramified stable-lattice transfer in arbitrary universes -/

@[expose] public noncomputable section
open Module IsLocalRing GaloisRepresentation TensorProduct
open scoped TensorProduct NumberField ThreeAdicPlan
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan

variable {O K W : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
  [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K]

/-- The lattice determinant maps to the generic-fibre determinant. -/
theorem lattice_det_universes (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (g : Field.absoluteGaloisGroup ℚ) :
    let := hΛ.isLattice
    algebraMap O K ((latticeGaloisRep ρK Λ hΛ hOK).det g) = (ρK g).det := by
  let := hΛ.isLattice
  let : ContinuousSMul O K := continuousSMul_of_algebraMap O K hOK.continuous
  obtain ⟨e, he⟩ := lattice_generic_equiv ρK Λ hΛ hOK
  have h := congrArg (fun σ : GaloisRep ℚ K W ↦ (σ g).det) he
  exact (LinearMap.det_baseChange (latticeGaloisRep ρK Λ hΛ hOK g) (A := K)).symm.trans
    ((LinearMap.det_conj ((latticeGaloisRep ρK Λ hΛ hOK g).baseChange K) e).symm.trans h)

/-- Inertia acting trivially on the generic fibre acts trivially on a lattice. -/
theorem lattice_unramified_universes (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (hρ : ρK.IsUnramifiedAt v) :
    (latticeGaloisRep ρK Λ hΛ hOK).IsUnramifiedAt v := by
  constructor
  intro g hg
  have hgK := hρ.localInertiaGroup_le hg
  change ρK.toLocal v g = 1 at hgK
  change (latticeGaloisRep ρK Λ hΛ hOK).toLocal v g = 1
  ext x
  change ρK.toLocal v g (x : W) = x
  rw [hgK]
  rfl

/-- All four hardly-ramified clauses are independent of the stable lattice. -/
theorem hardlyRamified_lattice_transfer_universes {p : ℕ} [Fact p.Prime] (hp : Odd p)
    [Algebra ℤ_[p] O] (ρK : GaloisRep ℚ K W) (Λ₀ Λ : Submodule O W)
    (h₀ : StableLattice.IsStableLattice ρK.toRepresentation Λ₀)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K))
    (h₀dim : Module.rank O Λ₀ = 2) (hΛdim : Module.rank O Λ = 2)
    (hρ : let := h₀.isLattice
      IsHardlyRamified hp h₀dim (latticeGaloisRep ρK Λ₀ h₀ hOK)) :
    let := hΛ.isLattice
    IsHardlyRamified hp hΛdim (latticeGaloisRep ρK Λ hΛ hOK) := by
  let := h₀.isLattice
  let := hΛ.isLattice
  let : ContinuousSMul O K := continuousSMul_of_algebraMap O K hOK.continuous
  refine ⟨?_, ?_, flat_of_stable_lattice_universes ρK Λ₀ Λ h₀ hΛ hOK _ hρ.isFlat,
    tame_two_of_stable_lattice ρK Λ₀ Λ h₀ hΛ hOK hρ.isTameAtTwo⟩
  · intro g
    apply IsFractionRing.injective O K
    rw [lattice_det_universes, ← lattice_det_universes ρK Λ₀ h₀ hOK, hρ.det]
  · intro q hq hgood
    have := hρ.isUnramified q hq hgood
    obtain ⟨e, he⟩ := lattice_generic_equiv ρK Λ₀ h₀ hOK
    have hK : ρK.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := by
      rw [← he]
      infer_instance
    exact lattice_unramified_universes ρK Λ hΛ hOK _ hK


end ThreeAdicPlan
