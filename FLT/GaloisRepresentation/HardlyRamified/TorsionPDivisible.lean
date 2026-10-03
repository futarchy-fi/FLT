/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionIntegralInclusions
public import FLT.GaloisRepresentation.HardlyRamified.TorsionLevelExactness
public import FLT.GaloisRepresentation.HardlyRamified.TorsionLevelRank
public import FLT.GroupScheme.IntegralKernelEquations
public import FLT.GroupScheme.PDivisibleSystem

/-!
# The p-divisible system of an original hardly ramified representation

Every defining property is proved for the chosen original HR models. No
compatibility, exactness, height, or p-divisible existence input is supplied.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)

/-- All ordered integral inclusions are closed immersions. -/
theorem torsionEmbedding_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (hρ.torsionEmbedding h) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [hρ.torsionEmbedding_eq_inclusion]
  exact hρ.torsionInclusion_surjective m d

omit [IsDomain R] in
/-- All ordered integral reductions are faithfully flat. -/
theorem torsionTransition_faithfullyFlat {m n : ℕ} (h : m ≤ n) :
    (hρ.torsionTransition h).toAlgHom.toRingHom.FaithfullyFlat := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  have hn : n = d + m := hd.trans (Nat.add_comm m d)
  clear hd
  subst n
  rw [hρ.torsionTransition_eq_reduction]
  exact hρ.torsionReduction_faithfullyFlat d m

/-- The actual lower inclusion is the scheme-theoretic kernel of reduction. -/
theorem torsion_augmentation_eq_inclusion_ker (m n : ℕ) :
    HopfAlgebra.augmentationIdeal (hρ.torsionReduction m n) =
      RingHom.ker (hρ.torsionInclusion m n).toAlgHom.toRingHom := by
  rw [ModelHom.ker_eq_closureIdeal _
    (by rw [genericHom_torsionInclusion]; exact hρ.torsionGenericInclusion_injective m n)
    (hρ.torsionInclusion_surjective m n), hρ.genericHom_torsionInclusion]
  exact hρ.torsion_actual_kernelIdeal_eq m n

/-- The original HR levels form a finite-flat p-divisible system of computed height. -/
def torsionPDivisible :
    PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p
      (torsionHeight (p := p) (R := R)) where
  level := hρ.torsionModel
  inclusion := hρ.torsionEmbedding
  reduction := hρ.torsionTransition
  inclusion_refl := hρ.torsionEmbedding_refl
  reduction_refl := hρ.torsionTransition_refl
  inclusion_comp := hρ.torsionEmbedding_comp
  reduction_comp := hρ.torsionTransition_comp
  closed := hρ.torsionEmbedding_surjective
  faithfullyFlat := hρ.torsionTransition_faithfullyFlat
  kernel m n := by
    rw [hρ.torsionEmbedding_eq_inclusion, hρ.torsionTransition_eq_reduction]
    exact hρ.torsion_augmentation_eq_inclusion_ker m n
  inclusion_reduction := hρ.torsionEmbedding_comp_transition
  reduction_inclusion := hρ.torsionTransition_comp_embedding
  killed := hρ.torsionModel_killed
  rank := hρ.torsionModel_finrank

end GaloisRepresentation.IsHardlyRamified
