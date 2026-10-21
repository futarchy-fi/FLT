/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterGroupBaseChange

/-!
# Comparing character groups from independent coefficient rings

Both sources identify with the same character scheme over the common ring.
The comparison preserves the actual group laws and is coherent for three
independent initial rings, without choices of coordinates or reduced supports.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CharacterSchemeBaseChange
universe u
variable (A B C G : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A C] [Algebra B C] [AddCommMonoid G]

/-- The full character sources from two initial rings compare over their common base. -/
def commonGroupIso : (Over.pullback (baseMap A C)).obj (model A G) ≅
    (Over.pullback (baseMap B C)).obj (model B G) :=
  (overIso A C G).symm ≪≫ overIso B C G

instance commonGroupIso_isMonHom : IsMonHom (commonGroupIso A B C G).hom := by
  dsimp only [commonGroupIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

instance commonGroupIso_inv_isMonHom : IsMonHom (commonGroupIso A B C G).inv := by
  dsimp only [commonGroupIso, Iso.trans_inv, Iso.symm_inv]
  infer_instance

/-- Comparison retains the actual recovery from the common character scheme. -/
@[reassoc] theorem commonGroupIso_recovery :
    (overIso A C G).hom ≫ (commonGroupIso A B C G).hom = (overIso B C G).hom := by
  simp only [commonGroupIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- Three independently based character sources compare transitively. -/
@[reassoc] theorem commonGroupIso_trans (D : Type u) [CommRing D] [Algebra D C] :
    (commonGroupIso A B C G).hom ≫ (commonGroupIso B D C G).hom =
      (commonGroupIso A D C G).hom := by
  simp only [commonGroupIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Comparing a source with itself is the identity on the entire pullback scheme. -/
theorem commonGroupIso_self : commonGroupIso A A C G = Iso.refl _ := by
  apply Iso.ext
  simp only [commonGroupIso, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id, Iso.refl_hom]

/-- Opposite comparisons are mutually inverse as actual relative scheme isomorphisms. -/
theorem commonGroupIso_symm : (commonGroupIso A B C G).symm = commonGroupIso B A C G := by
  apply Iso.ext
  rfl

end FLT.Mazur.CharacterSchemeBaseChange
