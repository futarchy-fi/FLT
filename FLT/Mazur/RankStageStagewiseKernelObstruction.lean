/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCompatibleKernelObstruction
public import FLT.Mazur.FiniteScalarObstruction

/-!
# Stagewise annihilation of the actual homogeneous numerator obstruction

Every all-order obstruction scalar passes each stage test. Geometry puts
the compatible norm in each stage ideal's radical, and hence supplies one
exponent for any finite set of stage tests. Neither an infinite exponent
bound nor compatible all-order lifts follow by reversing these comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance stageObstructionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance stageObstructionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance stageObstructionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)
attribute [local irreducible] rankStageCore rankStageNormParameter
  rankStageGlobalCoreRestriction rankStageInvariantTransition

/-- The stage scalar test, expressed over the same compatible global coefficient ring. -/
def rankStageEvaluatedNumeratorIdeal (k : ℕ) : Ideal (rankStageCompatibleInvariants e n) :=
  Ideal.comap (CompatibleRingTower.eval _ k)
    (HomogeneousNumeratorObstruction.scalarIdeal (rankStageGlobalCoreRestriction e n a ha k)
      (rankStageGlobalBoundaryKernel e n J k) (x.val k))

/-- An all-order compatible witness passes each separate stage test. -/
theorem rankStageCompatibleNumeratorIdeal_le_evaluated (k : ℕ) :
    rankStageCompatibleNumeratorIdeal e n a ha J x ≤
      rankStageEvaluatedNumeratorIdeal e n a ha J x k :=
  CompatibleRingTower.numeratorIdeal_le_stage _ _ _ _ _ _ k

variable (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (hC c) k) = ⊤)
  (hx : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (x.val k).val = 0)

include hx in
/-- Actual localization proves stagewise radical membership, with no uniform exponent assumed. -/
theorem rankStageCompatibleNorm_mem_evaluated_radical (k : ℕ) :
    rankStageCompatibleNorm e n a C hC hc ∈
      (rankStageEvaluatedNumeratorIdeal e n a ha J x k).radical := by
  obtain ⟨N, w, hw, he⟩ := exists_rankStageGlobalBoundaryKernel_numerator e n a ha
    J C hC hc k (x.val k) (hx k)
  refine ⟨N, w, hw, ?_⟩
  change rankStageGlobalCoreRestriction e n a ha k w =
    rankStageGlobalCoreRestriction e n a ha k (rankStageNormParameter e n C hC hc a k ^ N) *
      x.val k
  rw [map_pow]
  exact he

attribute [local irreducible] rankStageCompatibleNorm rankStageEvaluatedNumeratorIdeal

include hx in
/-- A finite set of stage tests has one power annihilating every scalar obstruction class. -/
theorem exists_rankStage_norm_power_finite_tests (T : Finset ℕ) :
    ∃ N : ℕ, ∀ k ∈ T, rankStageCompatibleNorm e n a C hC hc ^ N ∈
      rankStageEvaluatedNumeratorIdeal e n a ha J x k := by
  obtain ⟨N, hN⟩ := FiniteScalarObstruction.exists_uniform_power
    (fun k : T ↦ rankStageEvaluatedNumeratorIdeal e n a ha J x k.val)
    (rankStageCompatibleNorm e n a C hC hc)
    (fun k ↦ rankStageCompatibleNorm_mem_evaluated_radical e n a ha J x C hC hc hx k.val)
  exact ⟨N, fun k hk ↦ hN ⟨k, hk⟩⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
