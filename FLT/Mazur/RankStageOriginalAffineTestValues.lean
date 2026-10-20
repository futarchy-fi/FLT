/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalAffineRepresentatives
public import FLT.Mazur.IdealSheafAffineTestErrors

/-!
# Actual rank-core representatives on original affine tests

The original affine representatives evaluate to their prescribed full core
values on every closed test mapping to the core. This supplies the section
identity needed for boundary and mixed errors on unchanged test schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Pullback through an open subscheme evaluates its original section. -/
theorem openCore_section_pullback {Y Z : Scheme.{0}} (U : Y.Opens)
    (f : Z ⟶ U.toScheme) (h : ⊤ ≤ (f ≫ U.ι) ⁻¹ᵁ U) (v : Γ(U.toScheme, ⊤)) :
    (f ≫ U.ι).appLE U ⊤ h (U.topIso.hom v) = f.appTop v := by
  have hu : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have he := Scheme.Hom.appLE_comp_appLE f U.ι U ⊤ ⊤ U.ι_preimage_self.ge
    (by simp)
  rw [hu] at he
  have ht : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
  rw [ht] at he
  rw [← he]
  change f.appTop (U.topIso.inv (U.topIso.hom v)) = _
  exact congrArg f.appTop (U.topIso.commRingCatIsoToRingEquiv.symm_apply_apply v)

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance affineTestOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance affineTestOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance affineTestOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n) (k : ℕ)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha k
local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb
attribute [local irreducible] rankStageCore
/-- An actual original representative has the prescribed full core value on a closed test. -/
theorem rankStage_original_affine_test_value
    (h : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ rankStageCore e n a ha k)
  (v : Γ((C).toScheme, ⊤)) (w : Γ(X, U.1))
  (hw : (I ^ (k + 1)).subschemeι.app U.1 w =
    rankStageCoreAffineCoefficient e n a ha b hb k h v)
  {T : Scheme.{0}} (K : T.IdealSheafData) (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1)
  (z : (K ^ (k + 1)).subscheme ⟶ (C).toScheme)
  (hz : z ≫ (C).ι ≫ (I ^ (k + 1)).subschemeι = (K ^ (k + 1)).subschemeι ≫ g) :
    (K ^ (k + 1)).subschemeι.appTop (g.appLE U.1 ⊤ hg w) = z.appTop v := by
  let z' := z ≫ (C).ι
  have hz' : z' ≫ (I ^ (k + 1)).subschemeι = (K ^ (k + 1)).subschemeι ≫ g := by
    simpa only [z', Category.assoc] using hz
  rw [IdealSheafAffineTestErrors.representative_restrict I K (k + 1) U g hg z' hz', hw]
  unfold rankStageCoreAffineCoefficient
  have he := (z').map_appLE
    (IdealSheafAffineTestErrors.closed_domain I K (k + 1) U g hg z' hz') (homOfLE h).op
  exact (congrArg (fun r ↦ r ((C).topIso.hom v)) he).trans
    (openCore_section_pullback C z _ v)


end FLT.Mazur.EquivalenceRelationOrderedFrames
