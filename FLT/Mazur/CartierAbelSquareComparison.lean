/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelPulledSectionAdjoint
public import FLT.Mazur.SchemePullbackSquare

/-!
# The Cartier twist comparison is the original inverse square comparison

This identifies the independently defined comparison used by the geometric
Cartier pullback with the square used to construct the direct-image mate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.CartierAbel
open FCurve SchemePullbackSquare SheafPullbackPathComparison
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S T : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S)

/-- The original Cartier line comparison is the inverse of the mate's square comparison. -/
lemma twistSquareLineIso_eq_square (B : S.Modules) :
    twistSquareLineIso f g B =
      ((squareIso f (Limits.pullback.snd f g) g (Limits.pullback.fst f g)
        Limits.pullback.condition.symm).app B).symm := by
  have hc {Y Z : Scheme.{0}} {a b : Y ⟶ Z} (h : a = b) :
      pullbackCongr h = (pullbackCongr h.symm).symm := by
    subst b
    rfl
  apply Iso.ext
  simp only [twistSquareLineIso, squareIso, comparison, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Iso.app_hom]
  rw [hc (Limits.pullback.condition (f := f) (g := g))]
  rfl

/-- The actual pulled Cartier section has the tensor expression used by the square mate. -/
lemma pulledTwistedSection_square_section (L : X.Modules) (hL : LocallyFreeRankOne L)
    (s : RelativeSection f L hL) :
    (pulledTwistedSection f g L hL s).section_ =
      (ModuleSheafTensor.map (𝟙 _)
        ((squareIso f (Limits.pullback.snd f g) g (Limits.pullback.fst f g)
          Limits.pullback.condition.symm).inv.app s.val.baseLine.val)).app ⊤
        ((ModuleLineBundleTensorPullback.tensorIso (Limits.pullback.fst f g) L
          ((pullback f).obj s.val.baseLine.val)).hom.app ⊤
          (pullGlobal (Limits.pullback.fst f g) _ s.val.section_)) := by
  change (ModuleSheafTensor.map (𝟙 _) (twistSquareLineIso f g s.val.baseLine.val).hom).app
    ⊤ _ = _
  rw [twistSquareLineIso_eq_square]
  rfl

end FLT.Mazur.CartierAbel
