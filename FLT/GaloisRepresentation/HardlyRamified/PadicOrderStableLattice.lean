/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PadicOrderHardlyRamified

/-!
# General-prime normalized stable lattices

The constructed normalized HR model gives HR on each stable lattice in its
generic fibre. No family, splitting, or period comparison is assumed or produced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace PadicOrderPlan
open GaloisRepresentation

variable (p : ℕ) [Fact p.Prime] {R V : Type} [CommRing R] [Algebra ℤ_[p] R]
  [IsDomain R] [Module.Free ℤ_[p] R] [Module.Finite ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Free R V]

/-- Each normalized generic-fibre lattice retains the original rank two. -/
theorem normalized_lattice_rank_two (hV : Module.rank R V = 2)
    (Λ : Submodule (NormalizedOrder p R)
      (FractionRing R ⊗[NormalizedOrder p R] (NormalizedOrder p R ⊗[R] V)))
    [Submodule.IsLattice (FractionRing R) Λ] : Module.rank (NormalizedOrder p R) Λ = 2 := by
  rw [Submodule.IsLattice.rank' (FractionRing R), Module.rank_baseChange,
    Module.rank_baseChange, hV]
  simp

variable [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsModuleTopology ℤ_[p] R] [Module.Finite R V]

set_option maxHeartbeats 800000 in
-- Comparing the normalized field and nested tensor instances requires additional elaboration.
/-- Every stable lattice of the constructed normalized generic fibre is hardly ramified. -/
theorem hardlyRamified_of_stable_lattice (hpodd : Odd p) (hV : Module.rank R V = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hpodd hV ρ) :
    letI := fractionNormedField p R
    letI : TopologicalSpace (FractionRing R) :=
      (fractionNormedField p R).toUniformSpace.toTopologicalSpace
    letI : ContinuousSMul (NormalizedOrder p R) (FractionRing R) :=
      continuousSMul_of_algebraMap _ _ continuous_subtype_val
    ∀ (Λ : Submodule (NormalizedOrder p R)
      (FractionRing R ⊗[NormalizedOrder p R] (NormalizedOrder p R ⊗[R] V)))
      (hΛ : StableLattice.IsStableLattice
        ((ρ.baseChange (NormalizedOrder p R)).baseChange (FractionRing R)).toRepresentation Λ),
      letI := hΛ.isLattice
      IsHardlyRamified hpodd (normalized_lattice_rank_two p hV Λ)
        (ThreeAdicPlan.latticeGaloisRep
          ((ρ.baseChange (NormalizedOrder p R)).baseChange (FractionRing R))
          Λ hΛ Topology.IsInducing.subtypeVal) := by
  let := fractionNormedField p R
  let : TopologicalSpace (FractionRing R) :=
    (fractionNormedField p R).toUniformSpace.toTopologicalSpace
  let : ContinuousSMul (NormalizedOrder p R) (FractionRing R) :=
    continuousSMul_of_algebraMap _ _ continuous_subtype_val
  intro Λ hΛ
  let := hΛ.isLattice
  exact ThreeAdicPlan.hardlyRamified_of_integral_lattice hpodd _
    (hardlyRamified_normalization p hpodd hV hρ) Λ hΛ Topology.IsInducing.subtypeVal
    (normalized_lattice_rank_two p hV Λ)

end PadicOrderPlan
