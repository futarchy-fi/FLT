/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterSchemeBaseChange
public import FLT.Mazur.OverPullbackTowerExt

/-!
# First projection of a character map after coefficient extension

The intrinsic source comparison and the actual scheme pullback retain the
original character coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.CharacterSchemeBaseChange
universe u
variable (A B M : Type u) [CommRing A] [CommRing B] [Algebra A B] [AddCommMonoid M]

/-- Intrinsic coefficient extension preserves the first projection of every character map. -/
@[reassoc] theorem intrinsicMap_fst (X : Over (Spec (.of A))) (f : model A M ⟶ X) :
    ((overIso A B M).hom ≫ (Over.pullback (baseMap A B)).map f).left ≫
      pullback.fst X.hom (baseMap A B) =
        Spec.map (CommRingCat.ofHom (CharacterAlgebraScalarExtension.coeff A B M).toRingHom) ≫
          f.left := by
  rw [Over.comp_left, Category.assoc, OverPullbackCoherence.pullback_map_fst,
    overIso_fst_assoc]

end FLT.Mazur.CharacterSchemeBaseChange
