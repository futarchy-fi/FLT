/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RetainedLineSectionPullback

/-!
# The actual tensor isomorphism recovering a pulled retained section

Package tensor, square and dual comparisons as an isomorphism on the total
space. Its section formula retains geometric pullback of the original section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve DualAtlasLineQuotient ModuleSheafTensor DirectImageBaseChange SchemePullbackSquare
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
  moduleSheafDualPullbackIso ModuleLineBundleTensorPullback.tensorIso
variable {P X T S : Scheme.{0}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (L : X.Modules) (a : Line ((pushforward f).obj L))

/-- The actual tensor comparison to the pulled source's intrinsic dual twist. -/
@[irreducible] def retainedLinePullbackIso :
    (pullback p).obj (tensor L ((pullback f).obj (moduleSheafDual a.source))) ≅
      tensor ((pullback p).obj L)
        ((pullback q).obj (moduleSheafDual ((pullback g).obj a.source))) :=
  ModuleLineBundleTensorPullback.tensorIso p L _ ≪≫
    congr (Iso.refl _) ((squareIso f q g p w).app (moduleSheafDual a.source)).symm ≪≫
      congr (Iso.refl _) ((pullback q).mapIso (moduleSheafDualPullbackIso g a.rankOne))

/-- The packaged comparison carries the original pulled section to the retained one. -/
lemma retainedLinePullbackIso_section
    (e : (pullback g).obj ((pushforward f).obj L) ≅
      (pushforward q).obj ((pullback p).obj L))
    (he : e.hom = comparison p q f g w L) :
    (retainedLinePullbackIso p q f g w L a).hom.app ⊤
        (pullGlobal p _ (retainedLineSection f L a)) =
      retainedLineSection q ((pullback p).obj L) ((a.baseChange g).changeAmbient e) := by
  unfold retainedLinePullbackIso
  dsimp only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensor.congr, Iso.refl_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    TwistedSectionBaseChangeRegularity.section_]
  exact retainedLineSection_pullback p q f g w L a e he

end FLT.Mazur.CartierAbel
