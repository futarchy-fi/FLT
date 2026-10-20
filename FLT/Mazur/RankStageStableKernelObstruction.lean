/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageStableTransitions
public import FLT.Mazur.RankStageStagewiseKernelObstruction
public import FLT.Mazur.StableNumeratorObstruction

/-!
# All-order homogeneous annihilation on a stable rank stratum

Once the actual defining ideal powers stabilize, a single geometric stage
numerator gives ordinary compatible numerators at every order. This proves
norm radical membership in the all-order ideal, not just its stage tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance stableKernelOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance stableKernelOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance stableKernelOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n K : ℕ)
  (hK : ∀ l, K ≤ l → rankStratumIdeal (Over.mk p) n ^ (l + 1) =
    rankStratumIdeal (Over.mk p) n ^ (K + 1))
  (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
attribute [local irreducible] rankStageCore rankStageNormParameter
  rankStageInvariantTransition rankStageGlobalCoreRestriction rankStageCoreRestriction
  rankStageCompatibleNorm rankStageEvaluatedNumeratorIdeal

include hK hf in
/-- Stable geometry makes one stage radical test sufficient for all compatible orders. -/
theorem rankStageStable_mem_radical_iff (b : rankStageCompatibleInvariants e n) :
    b ∈ (rankStageCompatibleNumeratorIdeal e n a ha J x).radical ↔
      b.val K ∈ (HomogeneousNumeratorObstruction.scalarIdeal
        (rankStageGlobalCoreRestriction e n a ha K)
        (rankStageGlobalBoundaryKernel e n J K) (x.val K)).radical := by
  apply CompatibleRingTower.stable_mem_radical_numeratorIdeal_iff
  · intro k l m h h' z
    exact DFunLike.congr_fun (rankStageInvariantTransition_comp e n h h') z
  · exact fun l h ↦ rankStageInvariantTransition_bijective_of_power_eq e n h (hK l h)
  · intro l h
    exact ⟨rankStageCoreRestriction_injective_of_power_eq e n h (hK l h) a ha,
      rankStageCoreRestriction_surjective e n a ha f hf h⟩
  · exact fun _ _ h z hz ↦ rankStageGlobalBoundaryKernel_transition e n J h z hz
  · exact fun l h z hz ↦
      (rankStageGlobalBoundaryKernel_reflect_of_power_eq e n h (hK l h) J z).mp hz

variable (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (hC c) k) = ⊤)
  (hx : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (x.val k).val = 0)

include hK hf hx in
/-- The actual geometric norm annihilates the all-order obstruction by one power. -/
theorem rankStageCompatibleNorm_mem_radical_of_stable :
    rankStageCompatibleNorm e n a C hC hc ∈
      (rankStageCompatibleNumeratorIdeal e n a ha J x).radical := by
  apply (rankStageStable_mem_radical_iff e n K hK a ha J x f hf _).mpr
  obtain ⟨N, w, hw, he⟩ := exists_rankStageGlobalBoundaryKernel_numerator e n a ha
    J C hC hc K (x.val K) (hx K)
  refine ⟨N, w, hw, ?_⟩
  simpa only [rankStageCompatibleNorm, map_pow] using he

include hK hf hx in
/-- The bound supplies full homogeneous global numerators with unscaled order compatibility. -/
theorem exists_rankStage_uniform_kernel_tower_of_stable :
    ∃ (N : ℕ) (w : ∀ k, rankStageInvariants e n k),
      (∀ k, w k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ k l (h : k ≤ l), rankStageInvariantTransition e n h (w l) = w k) ∧
      ∀ k, rankStageGlobalCoreRestriction e n a ha k (w k) =
        (rankStageGlobalCoreRestriction e n a ha k
          (rankStageNormParameter e n C hC hc a k)) ^ N * x.val k :=
  (rankStageCompatibleNorm_mem_radical_iff e n a ha J x C hC hc).mp
    (rankStageCompatibleNorm_mem_radical_of_stable e n K hK a ha J x f hf C hC hc hx)

end FLT.Mazur.EquivalenceRelationOrderedFrames
