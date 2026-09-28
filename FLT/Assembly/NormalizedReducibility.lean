/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.ResidualQuotients

/-!
# Reducibility of the normalized three-adic generic fibre

The canonical normalized order supplies hardly ramified reductions on every
stable lattice, so integral sorting gives generic reducibility via Ribet's lemma.
-/

@[expose] public noncomputable section

open scoped TensorProduct ThreeAdicPlan
open IsLocalRing GaloisRepresentation

namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Normalization

variable {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]

set_option maxHeartbeats 800000 in
-- The normalized tensor tower requires additional instance and equality reductions.
/-- Integral sorting makes the normalized generic fibre reducible. -/
theorem normalized_not_isIrreducible_of_sortedExtensionExists
    (hsorted : SortedExtensionExists) (hV : Module.rank R V = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ) :
    ¬ ((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R)).IsIrreducible := by
  let instDiscrete : DiscreteTopology (ResidueField (NormalizedOrder R)) :=
    normalizedOrder_residue_discrete (R := R)
  obtain ⟨N⟩ := normalization_padic_order R
  obtain ⟨Λ₀, h₀, _, _⟩ := exists_initial_stable_lattice
    (ρ.baseChange (NormalizedOrder R))
    (K := FractionRing R) Topology.IsInducing.subtypeVal
  have hdim : Module.finrank (FractionRing R)
      (FractionRing R ⊗[NormalizedOrder R] (NormalizedOrder R ⊗[R] V)) = 2 := by
    apply Module.finrank_eq_of_rank_eq
    rw [Module.rank_baseChange, Module.rank_baseChange, hV]
    simp
  exact not_isIrreducible_of_sortedExtensionExists hsorted _ hdim Λ₀ h₀
    Topology.IsInducing.subtypeVal
    (fun Λ hΛ ↦ hardlyRamified_reduction_of_stable_lattice hV hρ N Λ hΛ)

end Normalization

end ThreeAdicPlan
