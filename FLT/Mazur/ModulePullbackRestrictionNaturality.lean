/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundlePullback

/-!
# Naturality of the geometric restriction-pullback comparison

The existing comparison is the component of an actual natural isomorphism.
It therefore preserves every original sheaf morphism in the geometric square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FCurve
variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ W)
variable (i : Z ⟶ X) (j : W ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
variable (h : i ≫ f = g ≫ j)

/-- Geometric restriction commutes with pullback as an isomorphism of actual functors. -/
def modulePullbackRestrictNatIso :
    pullback f ⋙ restrictFunctor i ≅ restrictFunctor j ⋙ pullback g :=
  Functor.isoWhiskerLeft (pullback f) (restrictFunctorIsoPullback i) ≪≫
    pullbackComp i f ≪≫ pullbackCongr h ≪≫ (pullbackComp g j).symm ≪≫
      Functor.isoWhiskerRight (restrictFunctorIsoPullback j).symm (pullback g)

/-- The functorial construction recovers the original geometric comparison exactly. -/
lemma modulePullbackRestrictNatIso_app (M : Y.Modules) :
    (modulePullbackRestrictNatIso f g i j h).app M =
      modulePullbackRestrictIso f g i j h M := rfl

/-- The actual restriction-pullback comparison preserves the original inclusion. -/
@[reassoc]
lemma modulePullbackRestrictIso_naturality {L M : Y.Modules} (s : L ⟶ M) :
    (restrictFunctor i).map ((pullback f).map s) ≫
        (modulePullbackRestrictIso f g i j h M).hom =
      (modulePullbackRestrictIso f g i j h L).hom ≫
        (pullback g).map ((restrictFunctor j).map s) :=
  (modulePullbackRestrictNatIso f g i j h).hom.naturality s

end FLT.Mazur.FCurve
