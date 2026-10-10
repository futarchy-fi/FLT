/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelIntegralFiberSections
public import FLT.Mazur.LineTensorSectionPullback
public import FLT.Mazur.LineTensorSectionTransport

/-!
# The adjoint of the independently pulled Cartier section

The geometric section from the Cartier construction is transported through
its actual tensor and square isomorphisms. Its dual-line morphism is
normalized without defining them by base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S T : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S)

/-- The original line-factor comparison in geometric pullback of a twisted section. -/
def twistSquareLineIso (B : S.Modules) :
    (pullback (Limits.pullback.fst f g)).obj ((pullback f).obj B) ≅
      (pullback (Limits.pullback.snd f g)).obj ((pullback g).obj B) :=
  (pullbackComp (Limits.pullback.fst f g) f).app B ≪≫
    (pullbackCongr Limits.pullback.condition).app B ≪≫
      ((pullbackComp (Limits.pullback.snd f g) g).app B).symm

/-- The existing twist comparison uses exactly this geometric line-factor isomorphism. -/
lemma twistBaseChangeIso_factor (L : X.Modules) (B : SchemePicard.LineBundle S) :
    twistBaseChangeIso f g L B =
      ModuleLineBundleTensorPullback.tensorIso (Limits.pullback.fst f g) L _ ≪≫
        congr (Iso.refl _) (twistSquareLineIso f g B.val) := rfl

variable (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The pulled section's dual-line map is the original map pulled and transported. -/
lemma pulledTwistedSection_dual_map (s : RelativeSection f L hL) :
    (lineHomSectionEquiv ((pullback (Limits.pullback.fst f g)).obj L)
        ((s.val.baseLine.property.pullback g).pullback (Limits.pullback.snd f g))).symm
        (pulledTwistedSection f g L hL s).section_ =
      (moduleSheafDualIso _ (twistSquareLineIso f g s.val.baseLine.val)).hom ≫
        (moduleSheafDualPullbackIso (Limits.pullback.fst f g)
          (s.val.baseLine.property.pullback f)).inv ≫
        (pullback (Limits.pullback.fst f g)).map
          ((lineHomSectionEquiv L (s.val.baseLine.property.pullback f)).symm
            s.val.section_) := by
  change (lineHomSectionEquiv _ _).symm
    ((map (𝟙 _) (twistSquareLineIso f g s.val.baseLine.val).hom).app ⊤
      ((ModuleLineBundleTensorPullback.tensorIso (Limits.pullback.fst f g) L _).hom.app ⊤
        (pullGlobal (Limits.pullback.fst f g) _ s.val.section_))) = _
  rw [lineHomSectionEquiv_symm_transport
    ((s.val.baseLine.property.pullback f).pullback (Limits.pullback.fst f g))]
  rw [lineHomSectionEquiv_symm_pullback _ (s.val.baseLine.property.pullback f)]

end FLT.Mazur.CartierAbel
