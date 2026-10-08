/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionLocalHom
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Image-open transitions from chart comparisons

A comparison between two chart modules on a common open subscheme induces
an isomorphism between their ambient pushforwards over the overlap image.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOverlapImageTransition

open SheafPullbackPathComparison ModuleSheafOpenImmersionLocalHom

variable {O X Y Z : Scheme.{u}}

/-- Pulling an open-immersion pushforward back recovers the original module. -/
def openCounitIso (i : Y ⟶ X) [IsOpenImmersion i] (M : Y.Modules) :
    (pullback i).obj ((pushforward i).obj M) ≅ M :=
  (restrictFunctorIsoPullback i).symm.app ((pushforward i).obj M) ≪≫
    (restrictFunctorAdjCounitIso i).app M

/-- Restrict an ambient chart pushforward to an overlap using its chart coordinate. -/
def coordinateIso (p : O ⟶ Y) (i : Y ⟶ X) [IsOpenImmersion i]
    (r : O ⟶ X) (h : p ≫ i = r) (M : Y.Modules) :
    (pullback r).obj ((pushforward i).obj M) ≅ (pullback p).obj M :=
  (comparison p i r h).symm.app ((pushforward i).obj M) ≪≫
    (pullback p).mapIso (openCounitIso i M)

variable (i : Y ⟶ X) (j : Z ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
variable (p : O ⟶ Y) (q : O ⟶ Z) (r : O ⟶ X)
variable (hi : p ≫ i = r) (hj : q ≫ j = r)
variable {M : Y.Modules} {N : Z.Modules}

/-- Regard a chart overlap comparison as a comparison of ambient pushforwards. -/
def ambientIso (e : (pullback p).obj M ≅ (pullback q).obj N) :
    (pullback r).obj ((pushforward i).obj M) ≅
      (pullback r).obj ((pushforward j).obj N) :=
  coordinateIso p i r hi M ≪≫ e ≪≫ (coordinateIso q j r hj N).symm

/-- The ambient comparison retains the original coordinate comparison. -/
@[reassoc]
lemma ambientIso_coordinate (e : (pullback p).obj M ≅ (pullback q).obj N) :
    (ambientIso i j p q r hi hj e).hom ≫ (coordinateIso q j r hj N).hom =
      (coordinateIso p i r hi M).hom ≫ e.hom := by
  simp only [ambientIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

variable [IsOpenImmersion r]

/-- Extending an invertible pullback map to the image gives an invertible map. -/
instance localHom_isIso {A B : X.Modules}
    (a : (pullback r).obj A ⟶ (pullback r).obj B) [IsIso a] :
    IsIso (localHom r a) := by
  unfold localHom ofRestriction toRestriction
  infer_instance

/-- The overlap comparison as an isomorphism on the slice over its image open. -/
def imageIso (e : (pullback p).obj M ≅ (pullback q).obj N) :
    ((pushforward i).obj M).over r.opensRange ≅
      ((pushforward j).obj N).over r.opensRange :=
  asIso (localHom r (ambientIso i j p q r hi hj e).hom)

/-- Passing to the image loses none of the ambient overlap comparison. -/
lemma imageIso_hom (e : (pullback p).obj M ≅ (pullback q).obj N) :
    (imageIso i j p q r hi hj e).hom =
      localHom r (ambientIso i j p q r hi hj e).hom := rfl

end FLT.Mazur.ModuleSheafOverlapImageTransition
