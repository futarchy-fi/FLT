/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImageChart

/-!
# Transporting chart maps to image opens

Pushforward through the chart's identification with its image transports
module morphisms and commutes with the ambient pushforward identification.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {M N : Y.Modules}

/-- A morphism between the transported modules on the image open. -/
def imageMap (f : M ⟶ N) : imageModule i M ⟶ imageModule i N :=
  (pushforward (imageIso i).hom).map f

/-- Transport of morphisms commutes with the ambient pushforward identification. -/
@[reassoc]
lemma imagePushforwardIso_naturality (f : M ⟶ N) :
    (pushforward i.opensRange.ι).map (imageMap i f) ≫ (imagePushforwardIso i N).hom =
      (imagePushforwardIso i M).hom ≫ (pushforward i).map f := by
  have h := ((pushforwardComp (imageIso i).hom i.opensRange.ι) ≪≫
    pushforwardCongr (imageIso_hom_ι i)).hom.naturality f
  exact h

/-- Recovering the original chart module also recovers its original morphism. -/
@[reassoc]
lemma imageRestrictionIso_naturality (f : M ⟶ N) :
    (restrictFunctor (imageIso i).hom).map (imageMap i f) ≫
        (imageRestrictionIso i N).hom = (imageRestrictionIso i M).hom ≫ f :=
  (restrictFunctorAdjCounitIso (imageIso i).hom).hom.naturality f

end FLT.Mazur.ModuleSheafOpenImageChart
