/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalPrincipalNumerators
public import FLT.Mazur.RankStageTopKernelObstruction

/-!
# All-order annihilation by an unchanged original invariant parameter

On a stable rank, original invariant principal domains have ordinary
compatible homogeneous numerators with one power of the original scalar.
At a top rank stabilization is constructed geometrically.
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
local instance originalStableOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance originalStableOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance originalStableOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (s : compatibleFunctions p q)
  (hs : A.basicOpen s.val ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n s.val hs)
  {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (hx : ∀ k, (rankStageCoreBoundaryIdeal e n s.val hs J k).subschemeι.appTop
    (x.val k).val = 0)
omit [IsAffine A] [LocallyQuasiFinite p] in
private theorem originalScalar_eval (k : ℕ) :
    (rankStageOriginalCompatibleScalars e n s).val k =
      rankStageOriginalInvariantRestriction e n k s := rfl

attribute [local irreducible] rankStageCore
  rankStageOriginalInvariantRestriction rankStageCompatibleNumeratorIdeal

include hf hx in
/-- Actual original scalar powers kill the full compatible obstruction on a stable rank. -/
theorem rankStageOriginalScalar_mem_radical_of_stable (K : ℕ)
    (hK : ∀ l, K ≤ l → rankStratumIdeal (Over.mk p) n ^ (l + 1) =
      rankStratumIdeal (Over.mk p) n ^ (K + 1)) :
    s ∈ (rankStageOriginalNumeratorIdeal e n s.val hs J x).radical := by
  change s ∈ (Ideal.comap (rankStageOriginalCompatibleScalars e n)
    (rankStageCompatibleNumeratorIdeal e n s.val hs J x)).radical
  rw [← Ideal.comap_radical]
  apply (rankStageStable_mem_radical_iff e n K hK s.val hs J x f hf _).mpr
  obtain ⟨N, w, hb, he⟩ :=
    exists_rankStage_original_scalar_numerator e n s hs K J (x.val K) (hx K)
  exact ⟨N, w, hb, by simpa only [map_pow, originalScalar_eval] using he⟩

include hf hx in
/-- Empty higher-frame image supplies original-scalar annihilation, with no norm replacement. -/
theorem rankStageOriginalScalar_mem_radical_of_next_empty
    (hn : rankImageOpen (Over.mk p) (n + 1) = ⊥) :
    s ∈ (rankStageOriginalNumeratorIdeal e n s.val hs J x).radical := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨K, hK⟩ := exists_rankStratum_stable_of_next_empty (Over.mk p) n hn
  exact rankStageOriginalScalar_mem_radical_of_stable e n s hs J x f hf hx K hK

end FLT.Mazur.EquivalenceRelationOrderedFrames
