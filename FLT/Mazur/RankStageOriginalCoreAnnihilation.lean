/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalCoreNumerators
public import FLT.Mazur.RankStageClopenKernelObstruction

/-!
# All-order original scalar annihilation on arbitrary principal cores

The chart parameter need not be invariant. A scalar in the original
invariant ring defining the core at a stable stage suffices to construct
one exponent and ordinary compatible homogeneous numerators at all orders.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coreStableOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coreStableOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coreStableOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)
  {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (s : compatibleFunctions p q)
  (hx : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (x.val k).val = 0)
attribute [local irreducible] rankStageCore rankStageOriginalInvariantRestriction
  rankStageCompatibleNumeratorIdeal

include hf hx in
/-- A stage core defined over original scalars yields an actual all-order annihilator. -/
theorem rankStageOriginalCoreScalar_mem_radical_of_stable (K : ℕ)
    (hK : ∀ l, K ≤ l → rankStratumIdeal (Over.mk p) n ^ (l + 1) =
      rankStratumIdeal (Over.mk p) n ^ (K + 1))
    (hs : rankStageCore e n a ha K = (rankThickening (Over.mk p) n K).basicOpen
      (rankStageOriginalInvariantRestriction e n K s).val) :
    s ∈ (rankStageOriginalNumeratorIdeal e n a ha J x).radical := by
  change s ∈ (Ideal.comap (rankStageOriginalCompatibleScalars e n)
    (rankStageCompatibleNumeratorIdeal e n a ha J x)).radical
  rw [← Ideal.comap_radical]
  apply (rankStageStable_mem_radical_iff e n K hK a ha J x f hf _).mpr
  obtain ⟨N, w, hb, he⟩ :=
    exists_rankStage_original_core_numerator e n a ha K J s hs (x.val K) (hx K)
  refine ⟨N, w, hb, ?_⟩
  change rankStageGlobalCoreRestriction e n a ha K w =
    rankStageGlobalCoreRestriction e n a ha K
      (rankStageOriginalInvariantRestriction e n K s ^ N) * x.val K
  simpa only [map_pow] using he

include hf hx in
/-- Closed higher-rank geometry supplies stabilization for an arbitrary original chart. -/
theorem rankStageOriginalCoreScalar_mem_radical_of_next_closed
    (hn : IsClosed (rankImageOpen (Over.mk p) (n + 1) : Set A))
    (hs : ∀ k, rankStageCore e n a ha k = (rankThickening (Over.mk p) n k).basicOpen
      (rankStageOriginalInvariantRestriction e n k s).val) :
    s ∈ (rankStageOriginalNumeratorIdeal e n a ha J x).radical := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨K, hK⟩ := exists_rankStratum_stable_of_next_closed (Over.mk p) n hn
  exact rankStageOriginalCoreScalar_mem_radical_of_stable e n a ha J x f hf s hx K hK (hs K)

end FLT.Mazur.EquivalenceRelationOrderedFrames
