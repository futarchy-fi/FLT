/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterSchemeSealedBaseChange
public import FLT.Mazur.CharacterSchemeBaseChangeMap

/-!
# Character maps along coefficient towers

Direct and iterated coefficient extension agree on the entire intrinsic
character map into any relative scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A B C M : Type) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [AddCommMonoid M]

/-- The opaque source comparison retains the original coefficient projection. -/
@[reassoc] theorem sourceIso_fst :
    (sourceIso A B M).hom.left ≫ Limits.pullback.fst (model A M).hom (baseMap A B) =
      Spec.map (CommRingCat.ofHom
        (CharacterAlgebraScalarExtension.coeff A B M).toRingHom) := by
  rw [sourceIso_def]
  exact overIso_fst A B M

/-- Opaque intrinsic coefficient extension preserves the original character map. -/
@[reassoc] theorem sourceMap_fst (X : Over (Spec (.of A))) (f : model A M ⟶ X) :
    ((sourceIso A B M).hom ≫ (Over.pullback (baseMap A B)).map f).left ≫
      Limits.pullback.fst X.hom (baseMap A B) =
        Spec.map (CommRingCat.ofHom
          (CharacterAlgebraScalarExtension.coeff A B M).toRingHom) ≫ f.left := by
  rw [Over.comp_left, Category.assoc, OverPullbackCoherence.pullback_map_fst,
    sourceIso_fst_assoc]

/-- A tower comparison preserving the original projection transports the full character map. -/
theorem sourceMap_comparison (X : Over (Spec (.of A))) (f : model A M ⟶ X)
    (d : (Over.pullback (baseMap A C)).obj X ⟶
      (Over.pullback (baseMap B C)).obj ((Over.pullback (baseMap A B)).obj X))
    (hd : d.left ≫ Limits.pullback.fst (Limits.pullback.snd X.hom (baseMap A B))
        (baseMap B C) ≫ Limits.pullback.fst X.hom (baseMap A B) =
      Limits.pullback.fst X.hom (baseMap A C)) :
    ((sourceIso A C M).hom ≫ (Over.pullback (baseMap A C)).map f) ≫ d =
    (sourceIso B C M).hom ≫ (Over.pullback (baseMap B C)).map
      ((sourceIso A B M).hom ≫ (Over.pullback (baseMap A B)).map f) := by
  apply OverPullbackCoherence.tower_hom_ext (baseMap A B) (baseMap B C) X
  rw [Over.comp_left, Category.assoc, hd, sourceMap_fst]
  have h := sourceMap_fst B C M ((Over.pullback (baseMap A B)).obj X)
    ((sourceIso A B M).hom ≫ (Over.pullback (baseMap A B)).map f)
  simp only [Over.pullback_obj_hom] at h
  rw [← Category.assoc, h, Category.assoc, sourceMap_fst]
  rw [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g) ≫ f.left)
    (coeff_tower A B C M).symm

end FLT.Mazur.CharacterSchemeBaseChange
