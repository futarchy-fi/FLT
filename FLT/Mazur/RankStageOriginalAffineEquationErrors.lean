/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalAffineTestValues
public import FLT.Mazur.RankStageOriginalAffineBoundaryTower

/-!
# Boundary and full mixed errors of original rank representatives

The full prescribed core boundary and the entire core relation force exact
ideal-power errors on original affine test schemes. The two mixed endpoints
may use independently chosen original affine representatives.
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
local instance affineErrorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance affineErrorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance affineErrorOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n) (k : ℕ)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha k
local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb
attribute [local irreducible] rankStageCore

/-- The original boundary discrepancy lies in the full test rank-ideal power. -/
theorem rankStage_original_boundary_test_error
    (h : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C)
    (J : A.IdealSheafData) (v : rankStageCoreInvariants e n a ha k)
    (t : Γ(J.subscheme, ⊤))
    (hv : (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t)
    (w : Γ(X, U.1))
    (hw : (I ^ (k + 1)).subschemeι.app U.1 w =
      rankStageCoreAffineCoefficient e n a ha b hb k h v.val)
    {T : Scheme.{0}} [IsAffine T] (K : T.IdealSheafData)
    (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1) (d : T ⟶ J.subscheme)
    (z : (K ^ (k + 1)).subscheme ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme)
    (hz : (z ≫ (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι) ≫
      (C).ι ≫ (I ^ (k + 1)).subschemeι = (K ^ (k + 1)).subschemeι ≫ g)
    (hd : z ≫ rankStageCoreOriginalBoundaryMap e n a ha J k =
      (K ^ (k + 1)).subschemeι ≫ d) :
    d.appTop t - g.appLE U.1 ⊤ hg w ∈ (K.ideal ⟨⊤, isAffineOpen_top T⟩) ^ (k + 1) := by
  change _ ∈ (K ^ (k + 1)).ideal ⟨⊤, isAffineOpen_top T⟩
  rw [← (K ^ (k + 1)).ker_subschemeι_app]
  change (K ^ (k + 1)).subschemeι.appTop _ = 0
  rw [map_sub, rankStage_original_affine_test_value e n a ha b hb k h v.val w hw K g hg
    (z ≫ (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι) hz]
  apply sub_eq_zero.mpr
  change (K ^ (k + 1)).subschemeι.appTop (d.appTop t) =
    z.appTop ((rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val)
  rw [hv]
  change ((K ^ (k + 1)).subschemeι ≫ d).appTop t =
    (z ≫ rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t
  rw [hd]

/-- Every full mixed test retains the exact error of two original representatives. -/
theorem rankStage_original_mixed_test_error
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
    {T : Scheme.{0}} [IsAffine T] (K : T.IdealSheafData)
    (g g' : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1)
    (hg' : ⊤ ≤ g' ⁻¹ᵁ (rankStageOriginalAffineOpen (p := p) n b' hb').1)
    (z : (K ^ (k + 1)).subscheme ⟶ (rankStageFirst (p := p) n k ⁻¹ᵁ C).toScheme)
    (hz : (z ≫ (rankStageFirst (p := p) n k).resLE C _ le_rfl) ≫
      (C).ι ≫ (I ^ (k + 1)).subschemeι = (K ^ (k + 1)).subschemeι ≫ g)
    (hz' : (z ≫ (rankStageSecond e n k).resLE C _
      (rankStageCore_invariant e n a ha k).le) ≫
        (C).ι ≫ (I ^ (k + 1)).subschemeι = (K ^ (k + 1)).subschemeι ≫ g') :
    g.appLE U.1 ⊤ hg w -
      g'.appLE (rankStageOriginalAffineOpen (p := p) n b' hb').1 ⊤ hg' w' ∈
        (K.ideal ⟨⊤, isAffineOpen_top T⟩) ^ (k + 1) := by
  change _ ∈ (K ^ (k + 1)).ideal ⟨⊤, isAffineOpen_top T⟩
  rw [← (K ^ (k + 1)).ker_subschemeι_app]
  change (K ^ (k + 1)).subschemeι.appTop _ = 0
  rw [map_sub, rankStage_original_affine_test_value e n a ha b hb k h v.val w hw K g hg
    _ hz, rankStage_original_affine_test_value e n a ha b' hb' k h' v.val w' hw' K g' hg'
      _ hz']
  apply sub_eq_zero.mpr
  exact congrArg z.appTop v.property

end FLT.Mazur.EquivalenceRelationOrderedFrames
