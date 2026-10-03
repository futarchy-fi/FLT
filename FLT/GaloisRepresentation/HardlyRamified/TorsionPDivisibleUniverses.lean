/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionInclusionsUniverses
public import FLT.GaloisRepresentation.HardlyRamified.TorsionExactnessUniverses
public import FLT.GaloisRepresentation.HardlyRamified.TorsionRankUniverses
public import FLT.GroupScheme.IntegralKernelEquations
public import FLT.GroupScheme.PDivisibleSystem

/-!
# Arbitrary-universe The p-divisible system of an original hardly ramified representation

Every defining property is proved for the chosen original HR models. No
compatibility, exactness, height, or p-divisible existence input is supplied.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)

/-- All ordered integral inclusions are closed immersions. -/
theorem torsionEmbedding_surjective_universes {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (hρ.torsionEmbeddingUniverses h) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [hρ.torsionEmbedding_eq_inclusion_universes]
  exact hρ.torsionInclusion_surjective_universes m d

omit [IsDomain R] in
/-- All ordered integral reductions are faithfully flat. -/
theorem torsionTransition_faithfullyFlat_universes {m n : ℕ} (h : m ≤ n) :
    (hρ.torsionTransitionUniverses h).toAlgHom.toRingHom.FaithfullyFlat := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  have hn : n = d + m := hd.trans (Nat.add_comm m d)
  clear hd
  subst n
  rw [hρ.torsionTransition_eq_reduction_universes]
  exact hρ.torsionReduction_faithfullyFlat_universes d m

/-- The actual lower inclusion is the scheme-theoretic kernel of reduction. -/
theorem torsion_augmentation_eq_inclusion_ker_universes (m n : ℕ) :
    HopfAlgebra.augmentationIdeal (hρ.torsionReductionUniverses m n) =
      RingHom.ker (hρ.torsionInclusionUniverses m n).toAlgHom.toRingHom := by
  rw [ModelHom.ker_eq_closureIdeal _
    (by
      rw [genericHom_torsionInclusionUniverses]
      exact hρ.torsionGenericInclusion_injective_universes m n)
    (hρ.torsionInclusion_surjective_universes m n), hρ.genericHom_torsionInclusionUniverses]
  exact hρ.torsion_actual_kernelIdeal_eq_universes m n

/-- The original HR levels form a finite-flat p-divisible system of computed height. -/
def torsionPDivisibleUniverses :
    PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p
      (torsionHeightUniverses (p := p) (R := R)) where
  level := hρ.torsionModelUniverses
  inclusion := hρ.torsionEmbeddingUniverses
  reduction := hρ.torsionTransitionUniverses
  inclusion_refl := hρ.torsionEmbedding_refl_universes
  reduction_refl := hρ.torsionTransition_refl_universes
  inclusion_comp := hρ.torsionEmbedding_comp_universes
  reduction_comp := hρ.torsionTransition_comp_universes
  closed := hρ.torsionEmbedding_surjective_universes
  faithfullyFlat := hρ.torsionTransition_faithfullyFlat_universes
  kernel m n := by
    rw [hρ.torsionEmbedding_eq_inclusion_universes, hρ.torsionTransition_eq_reduction_universes]
    exact hρ.torsion_augmentation_eq_inclusion_ker_universes m n
  inclusion_reduction := hρ.torsionEmbedding_comp_transition_universes
  reduction_inclusion := hρ.torsionTransition_comp_embedding_universes
  killed := hρ.torsionModel_killed_universes
  rank := hρ.torsionModel_finrank_universes

end GaloisRepresentation.IsHardlyRamified
