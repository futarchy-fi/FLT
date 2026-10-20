/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageStableKernelObstruction
public import FLT.Mazur.RankStratumTopNilpotence

/-!
# Geometric all-order annihilation at a top rank

Absence of larger frames gives a uniform nilpotence threshold on the whole
rank-image open. The stable-stage argument therefore applies to every full
homogeneous core tower, with no supplied stabilization or power witness.
Lower ranks with nonempty higher-frame loci require further arguments.
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
local instance topKernelOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance topKernelOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance topKernelOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (hn : rankImageOpen (Over.mk p) (n + 1) = ⊥)
  (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (hC c) k) = ⊤)
  (hx : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (x.val k).val = 0)
attribute [local irreducible] rankStageCore rankStageNormParameter
  rankStageCompatibleNorm rankStageCompatibleNumeratorIdeal

include hn hf hx in
/-- On the top rank, geometry places the norm in the actual all-order obstruction radical. -/
theorem rankStageCompatibleNorm_mem_radical_of_next_empty :
    rankStageCompatibleNorm e n a C hC hc ∈
      (rankStageCompatibleNumeratorIdeal e n a ha J x).radical := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨K, hK⟩ := exists_rankStratum_stable_of_next_empty (Over.mk p) n hn
  exact rankStageCompatibleNorm_mem_radical_of_stable e n K hK a ha J x f hf C hC hc hx

include hn hf hx in
/-- One exponent extends the entire homogeneous tower at a top rank with ordinary compatibility. -/
theorem exists_rankStage_uniform_kernel_tower_of_next_empty :
    ∃ (N : ℕ) (w : ∀ k, rankStageInvariants e n k),
      (∀ k, w k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ k l (h : k ≤ l), rankStageInvariantTransition e n h (w l) = w k) ∧
      ∀ k, rankStageGlobalCoreRestriction e n a ha k (w k) =
        (rankStageGlobalCoreRestriction e n a ha k
          (rankStageNormParameter e n C hC hc a k)) ^ N * x.val k :=
  (rankStageCompatibleNorm_mem_radical_iff e n a ha J x C hC hc).mp
    (rankStageCompatibleNorm_mem_radical_of_next_empty e n hn a ha J x f hf C hC hc hx)

end FLT.Mazur.EquivalenceRelationOrderedFrames
