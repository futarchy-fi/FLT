/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryRelabelNormalization

/-!
# The actual finite relabeling action on the normalized auxiliary slice

Relabeling followed by normalization defines an automorphism of the original
closed slice. Absorption of intermediate normalization proves the group laws
and equivariance of the normalization morphism on arbitrary scheme families.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] auxiliaryNormalizationMorphism normalizedSliceInclusion
  auxiliarySchemeNormalizedSlicePoint

/-- Relabel an actual slice point and return it to its canonical frame. -/
def normalizedAuxiliaryRelabel (e : MulAut (Labels 4)) : normalizedSlice ⟶ normalizedSlice :=
  normalizedSliceInclusion ≫ (auxiliaryAction 4 e).hom ≫ auxiliaryNormalizationMorphism

/-- The original normalization morphism intertwines relabeling on both schemes. -/
@[reassoc] theorem auxiliaryNormalizationMorphism_equivariant (e : MulAut (Labels 4)) :
    auxiliaryNormalizationMorphism ≫ normalizedAuxiliaryRelabel e =
      (auxiliaryAction 4 e).hom ≫ auxiliaryNormalizationMorphism :=
  auxiliaryNormalizationMorphism_relabel e

/-- The identity label automorphism acts identically on the original closed slice. -/
@[simp] theorem normalizedAuxiliaryRelabel_one : normalizedAuxiliaryRelabel 1 = 𝟙 _ := by
  rw [normalizedAuxiliaryRelabel, map_one]
  change normalizedSliceInclusion ≫ 𝟙 _ ≫ auxiliaryNormalizationMorphism = _
  rw [Category.id_comp, normalizedSliceInclusion_normalization]

/-- The normalized morphisms satisfy the left-action composition convention. -/
theorem normalizedAuxiliaryRelabel_mul (e d : MulAut (Labels 4)) :
    normalizedAuxiliaryRelabel (e * d) =
      normalizedAuxiliaryRelabel d ≫ normalizedAuxiliaryRelabel e := by
  unfold normalizedAuxiliaryRelabel
  rw [Category.assoc, Category.assoc, auxiliaryNormalizationMorphism_relabel]
  have h : (auxiliaryAction 4 (e * d)).hom =
      (auxiliaryAction 4 d).hom ≫ (auxiliaryAction 4 e).hom :=
    congrArg Iso.hom ((auxiliaryAction 4).map_mul e d)
  rw [h, Category.assoc]

/-- Relabeling by the inverse reverses the actual normalized morphism. -/
def normalizedAuxiliaryRelabelAut (e : MulAut (Labels 4)) : Aut normalizedSlice where
  hom := normalizedAuxiliaryRelabel e
  inv := normalizedAuxiliaryRelabel e⁻¹
  hom_inv_id := by rw [← normalizedAuxiliaryRelabel_mul, inv_mul_cancel,
    normalizedAuxiliaryRelabel_one]
  inv_hom_id := by rw [← normalizedAuxiliaryRelabel_mul, mul_inv_cancel,
    normalizedAuxiliaryRelabel_one]

/-- The actual finite label group acts on the original normalized slice. -/
def normalizedAuxiliaryAction : MulAut (Labels 4) →* Aut normalizedSlice where
  toFun := normalizedAuxiliaryRelabelAut
  map_one' := by
    apply Aut.ext
    exact normalizedAuxiliaryRelabel_one
  map_mul' e d := by
    apply Aut.ext
    exact normalizedAuxiliaryRelabel_mul e d

/-- Normalizing any relabeled scheme family is the action on its normalized slice point. -/
theorem auxiliarySchemeNormalizedSlicePoint_action {T : Scheme}
    (f : T ⟶ levelFour.left) (e : MulAut (Labels 4)) :
    auxiliarySchemeNormalizedSlicePoint (f ≫ (auxiliaryAction 4 e).hom) =
      auxiliarySchemeNormalizedSlicePoint f ≫ (normalizedAuxiliaryAction e).hom := by
  rw [← auxiliaryNormalizationMorphism_comp, ← auxiliaryNormalizationMorphism_comp,
    Category.assoc]
  exact congrArg (f ≫ ·) (auxiliaryNormalizationMorphism_equivariant e).symm

end FLT.Mazur.UniversalWeierstrass
