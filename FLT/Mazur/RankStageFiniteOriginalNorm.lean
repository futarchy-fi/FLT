/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationOriginalNormCore
public import FLT.Mazur.RankStageOriginalCoreAnnihilation
public import FLT.Mazur.RelativeFiniteFrameRankClosed

/-!
# Constructed original norm annihilators for every finite-relation rank

Arbitrary original chart parameters define the same cores after replacing
only the scalar by its whole original relation norm. Finiteness constructs
closed higher-rank loci and actual stabilization. Neither invariant chart
parameters nor supplied closedness nor norm descent is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections FiniteFlatRelationNormCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] [IsFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance finiteNormOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteNormOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteNormOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance finiteNormOver_finite : IsFinite (Over.mk p).hom := ‹IsFinite p›
/-- The whole original relation norm, with source affineness constructed from finiteness. -/
def rankStageOriginalNorm (a : Γ(A, ⊤)) : compatibleFunctions p q := by
  let _ : IsAffine D := isAffine_of_isAffineHom p
  exact coefficient p q e a
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)

/-- The original norm defines the unchanged arbitrary core at every full rank order. -/
theorem rankStageCore_eq_basicOpen_originalNorm (k : ℕ) :
    rankStageCore e n a ha k = (rankThickening (Over.mk p) n k).basicOpen
      (rankStageOriginalInvariantRestriction e n k (rankStageOriginalNorm e a)).val := by
  let _ : IsAffine D := isAffine_of_isAffineHom p
  let _ := rankStageFirst_finite (p := p) n k
  exact FiniteRelationOriginalNormCore.core_eq_basicOpen_pullback p q e
    (rankStageFirst (p := p) n k) (rankStageSecond e n k) (rankStageEquivalence e n k)
    (rankThickeningMap (Over.mk p) n k) (rankStageArrow (p := p) n k)
    (rankStageFirst_isPullback n k) (rankStageSecond_map e n k).symm a
    (rankStagePrincipal_affine n a ha k)

attribute [local irreducible] rankStageCore rankStageOriginalInvariantRestriction
  rankStageOriginalNorm
variable (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)
  {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (hx : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (x.val k).val = 0)

include hf hx in
/-- A constructed original norm kills the actual all-order full homogeneous obstruction. -/
theorem rankStageOriginalNorm_mem_radical_of_finite :
    rankStageOriginalNorm e a ∈ (rankStageOriginalNumeratorIdeal e n a ha J x).radical := by
  exact rankStageOriginalCoreScalar_mem_radical_of_next_closed e n a ha J x f hf
    (rankStageOriginalNorm e a) hx (rankImageOpen_isClosed_of_finite (Over.mk p) (n + 1))
    (rankStageCore_eq_basicOpen_originalNorm e n a ha)

end FLT.Mazur.EquivalenceRelationOrderedFrames
