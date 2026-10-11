/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationActionPoints
public import FLT.Mazur.WeierstrassGlobalModificationContractionFlatExt

/-!
# Zero acts identically on the whole modification

Compare the lifted zero action with the identity through the actual
contraction. Flat-reference uniqueness proves the equality on the entire
modified cubic, including its exceptional points. Naturality then gives the
identity on every scheme-valued point, without flatness of that point.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The actual lifted zero action fixes the entire modified cubic as a scheme morphism. -/
theorem smoothPointAction_zero_id :
    smoothPointAction W s b3 b4 b6 h3 h4 h6 hs
        (structureMap W s b3 b4 b6 h3 h4 h6 hs ≫ integralSmoothZero W) (𝟙 _)
        (by rw [Category.assoc, integralSmoothZero_structure, Category.comp_id,
          Category.id_comp]) = 𝟙 _ := by
  apply contraction_ext_of_flat W s b3 b4 b6 h3 h4 h6 hs (𝟙 _)
  rw [smoothPointAction_contraction]
  simp only [Category.id_comp, structureMap, Category.assoc]
  exact leftSmoothPointAddition_zero W _ _

/-- Every scheme-valued point of the entire modification is fixed by the actual smooth zero. -/
theorem smoothPointAction_zero {T : Scheme.{u}}
    (b : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (h : (b ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs ≫ integralSmoothZero W) ≫
      integralSmoothStructure W = b ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs) :
    smoothPointAction W s b3 b4 b6 h3 h4 h6 hs
      (b ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs ≫ integralSmoothZero W) b h = b := by
  have he := smoothPointAction_comp W s b3 b4 b6 h3 h4 h6 hs b
    (structureMap W s b3 b4 b6 h3 h4 h6 hs ≫ integralSmoothZero W) (𝟙 _)
    (by rw [Category.assoc, integralSmoothZero_structure, Category.comp_id, Category.id_comp])
  simpa only [Category.comp_id, smoothPointAction_zero_id] using he

end FLT.Mazur.WeierstrassGlobalModification
