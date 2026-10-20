/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalBoundaryTests
public import FLT.Mazur.RankStageOriginalMixedCoreTests

/-!
# Original coordinate errors from constructed closed tests

Only the original boundary and relation squares are input. The full closed
tests, both endpoint squares and exact rank-power kernels are constructed,
so these errors apply uniformly to every original coordinate in the core.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance constructedErrorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance constructedErrorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance constructedErrorOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n) (k : ℕ)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha k
local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb
attribute [local irreducible] rankStageCore


/-- The original boundary square alone gives the exact pulled rank-power error. -/
theorem rankStage_original_boundary_error
    (h : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C)
    (J : A.IdealSheafData) (v : rankStageCoreInvariants e n a ha k)
    (t : Γ(J.subscheme, ⊤))
    (hv : (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t)
    (w : Γ(X, U.1))
    (hw : (I ^ (k + 1)).subschemeι.app U.1 w =
      rankStageCoreAffineCoefficient e n a ha b hb k h v.val)
    {T : Scheme.{0}} [IsAffine T] (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1)
    (d : T ⟶ J.subscheme)
    (hd : g ≫ (rankImageOpen (Over.mk p) n).ι = d ≫ J.subschemeι) :
    d.appTop t - g.appLE U.1 ⊤ hg w ∈
      (((I).comap g).ideal ⟨⊤, isAffineOpen_top T⟩) ^ (k + 1) :=
  rankStage_original_boundary_test_error e n a ha b hb k h J v t hv w hw
    ((I).comap g) g hg d (rankStageOriginalBoundaryTest e n a ha b hb k h J g hg d hd)
    (rankStageOriginalBoundaryTest_source e n a ha b hb k h J g hg d hd)
    (rankStageOriginalBoundaryTest_boundary e n a ha b hb k h J g hg d hd)

/-- Two original relation endpoints give the exact mixed error without supplied test maps. -/
theorem rankStage_original_mixed_error
    (h : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C)
    (b' : Γ(A, ⊤)) (hb' : A.basicOpen b' ≤ rankImageOpen (Over.mk p) n)
    (h' : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b' ≤ C)
    (v : rankStageCoreInvariants e n a ha k)
    (w : Γ(X, U.1))
    (w' : Γ(X, (rankStageOriginalAffineOpen (p := p) n b' hb').1))
    (hw : (I ^ (k + 1)).subschemeι.app U.1 w =
      rankStageCoreAffineCoefficient e n a ha b hb k h v.val)
    (hw' : (I ^ (k + 1)).subschemeι.app
      (rankStageOriginalAffineOpen (p := p) n b' hb').1 w' =
        rankStageCoreAffineCoefficient e n a ha b' hb' k h' v.val)
    {T : Scheme.{0}} [IsAffine T] (g g' : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1)
    (hg' : ⊤ ≤ g' ⁻¹ᵁ (rankStageOriginalAffineOpen (p := p) n b' hb').1)
    (δ : T ⟶ D) (hδ : δ ≫ p = g ≫ (rankImageOpen (Over.mk p) n).ι)
    (hδ' : δ ≫ q = g' ≫ (rankImageOpen (Over.mk p) n).ι) :
    g.appLE U.1 ⊤ hg w -
      g'.appLE (rankStageOriginalAffineOpen (p := p) n b' hb').1 ⊤ hg' w' ∈
        (((I).comap g).ideal ⟨⊤, isAffineOpen_top T⟩) ^ (k + 1) :=
  rankStage_original_mixed_test_error e n a ha b hb k h b' hb' h' v w w' hw hw'
    ((I).comap g) g g' hg hg' (rankStageOriginalMixedCoreTest e n a ha b hb k h g hg δ hδ)
    (rankStageOriginalMixedCoreTest_first e n a ha b hb k h g hg δ hδ)
    (rankStageOriginalMixedCoreTest_second e n a ha b hb k h g g' hg δ hδ hδ')

end FLT.Mazur.EquivalenceRelationOrderedFrames
