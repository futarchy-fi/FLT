/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingSchemeNormalizedGroup
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeMarking
public import FLT.Mazur.GroupSchemeBaseChangeComparison

/-!
# The original boundary comparison retains every auxiliary label

The already constructed arbitrary-source auxiliary comparison carries the
actual universal labeling to the unchanged original boundary marking.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The inverse coefficient comparison retains both original projections. -/
theorem coefficientInverseComparison_fst {S T U : Scheme} (f : U ⟶ T) (g : T ⟶ S)
    (k : U ⟶ S) (h : k = f ≫ g) (G : CommGrp (Over S)) (H : CommGrp (Over T))
    (e : H ≅ (Over.pullback g).mapCommGrp.obj G) :
    ((congrIso h G ≪≫ compIso f g G ≪≫
      (Over.pullback f).mapCommGrp.mapIso e.symm).inv.hom.hom.hom.left) ≫
        pullback.fst G.X.hom k =
          pullback.fst H.X.hom f ≫ e.hom.hom.hom.hom.left ≫ pullback.fst G.X.hom g :=
  coefficientComparison_fst f g k h.symm G H e

end FLT.Mazur.GroupSchemeBaseChange

namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  {T : Scheme} (j : T ⟶ smoothAuxiliaryOverlap t h₂ ht hf)

/-- The inverse auxiliary comparison retains the original universal family projection. -/
theorem smoothSchemeAuxiliaryGroupIso_inv_fst :
    (smoothSchemeAuxiliaryGroupIso t h₂ ht hf j).inv.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom
        ((j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≫ levelFour.hom) =
          pullback.fst (family t).hom (j ≫ smoothAuxiliaryProjection t h₂ ht hf) ≫
            smoothUniversalMorphism t h₂ ht hf := by
  rw [smoothSchemeAuxiliaryGroupIso_def]
  let b := j ≫ smoothAuxiliaryProjection t h₂ ht hf
  let c := Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf))
  let h : (j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≫ levelFour.hom = b ≫ c :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => j ≫ k) (smoothAuxiliaryPoint_base t h₂ ht hf)).trans
        (Category.assoc _ _ _).symm)
  let e : smoothGroup t ht hf ≅ (Over.pullback c).mapCommGrp.obj
      (integralCurveGroup smoothEquation smoothEquation_discriminant) :=
    smoothUniversalGroupIso t h₂ ht hf
  have hc := GroupSchemeBaseChange.coefficientInverseComparison_fst b c
    ((j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≫ levelFour.hom) h
    (integralCurveGroup smoothEquation smoothEquation_discriminant) (smoothGroup t ht hf) e
  exact hc.trans (congrArg (fun z => pullback.fst (family t).hom b ≫ z)
    (smoothUniversalGroupIso_fst t h₂ ht hf))

/-- Every original boundary label returns to its actual displayed universal section. -/
theorem smoothSchemeAuxiliaryGroupIso_inv_marking (a : Labels 4) :
    smoothOverlapMarking t h₂ ht hf j a ≫
      (smoothSchemeAuxiliaryGroupIso t h₂ ht hf j).inv.hom.hom.hom =
        auxiliarySchemeMarking (j ≫ smoothAuxiliaryPoint t h₂ ht hf) a := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc, smoothSchemeAuxiliaryGroupIso_inv_fst]
  exact smoothOverlapMarking_universal t h₂ ht hf j a

/-- The actual universal labeling maps to the original boundary marking, label by label. -/
theorem smoothSchemeAuxiliaryGroupIso_marking (a : Labels 4) :
    auxiliarySchemeMarking (j ≫ smoothAuxiliaryPoint t h₂ ht hf) a ≫
      (smoothSchemeAuxiliaryGroupIso t h₂ ht hf j).hom.hom.hom.hom =
        smoothOverlapMarking t h₂ ht hf j a := by
  rw [← smoothSchemeAuxiliaryGroupIso_inv_marking, Category.assoc]
  have h : (smoothSchemeAuxiliaryGroupIso t h₂ ht hf j).inv.hom.hom.hom ≫
      (smoothSchemeAuxiliaryGroupIso t h₂ ht hf j).hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun e => e.hom.hom.hom)
      (smoothSchemeAuxiliaryGroupIso t h₂ ht hf j).inv_hom_id
  rw [h, Category.comp_id]

end FLT.Mazur.OneGonSmoothing
