/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafClosedCoreTests
public import FLT.Mazur.RankStageOriginalAffineEquationErrors

/-!
# Constructing full original boundary tests

Every original affine boundary coordinate has a canonical closed test in the
core boundary. Both squares follow from the original boundary square and the
actual ideal pullback, rather than being supplied as test data.
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
local instance boundaryTestOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryTestOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryTestOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n) (k : ℕ)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha k
local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb
attribute [local irreducible] rankStageCore


variable (h : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ rankStageCore e n a ha k)
  (J : A.IdealSheafData) {T : Scheme.{0}} (g : T ⟶ (rankImageOpen (Over.mk p) n).toScheme)
  (hg : ⊤ ≤ g ⁻¹ᵁ (rankStageOriginalAffineOpen (p := p) n b hb).1)
  (d : T ⟶ J.subscheme) (hd : g ≫ (rankImageOpen (Over.mk p) n).ι = d ≫ J.subschemeι)
local notation "K" => (I).comap g
local notation "B" => rankStageCoreBoundaryIdeal e n a ha J k
local notation "z" => IdealSheafClosedCoreTests.coreMap I (k + 1) U C h g hg

include hd in
/-- The canonical core test commutes with the original boundary inclusion. -/
theorem rankStage_boundary_core_square :
    z ≫ rankStageCoreOriginalMap e n a ha k =
      (K ^ (k + 1)).subschemeι ≫ d ≫ J.subschemeι := by
  rw [rankStageCoreOriginalMap, rankThickeningMap,
    IdealSheafClosedCoreTests.coreMap_inclusion_assoc, hd]

/-- The full closed test in the core boundary, constructed from the original square. -/
def rankStageOriginalBoundaryTest :
    (K ^ (k + 1)).subscheme ⟶ (B).subscheme :=
  (IdealSheafClosedTransitions.isPullback B J
    (rankStageCoreOriginalMap e n a ha k)
    (rankStageCoreOriginalMap_ideal e n a ha J k)).lift z
      ((K ^ (k + 1)).subschemeι ≫ d)
      (rankStage_boundary_core_square e n a ha b hb k h J g hg d hd)

/-- The constructed boundary test retains the original source square. -/
@[reassoc]
theorem rankStageOriginalBoundaryTest_source :
    (rankStageOriginalBoundaryTest e n a ha b hb k h J g hg d hd ≫ (B).subschemeι) ≫
      (C).ι ≫ (I ^ (k + 1)).subschemeι = (K ^ (k + 1)).subschemeι ≫ g := by
  rw [rankStageOriginalBoundaryTest, CategoryTheory.IsPullback.lift_fst]
  exact IdealSheafClosedCoreTests.coreMap_inclusion I (k + 1) U C h g hg

/-- The constructed boundary test retains the unchanged original boundary map. -/
@[reassoc]
theorem rankStageOriginalBoundaryTest_boundary :
    rankStageOriginalBoundaryTest e n a ha b hb k h J g hg d hd ≫
      rankStageCoreOriginalBoundaryMap e n a ha J k =
        (K ^ (k + 1)).subschemeι ≫ d := by
  exact CategoryTheory.IsPullback.lift_snd _ _ _ _

end FLT.Mazur.EquivalenceRelationOrderedFrames
