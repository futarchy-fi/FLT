/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonParameterIso
public import FLT.Mazur.OneGonCoefficientTowerProjection
public import FLT.Mazur.OneGonSmoothCoefficientTower
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Iterated arithmetic coefficient recovery

The independently constructed coefficient isomorphisms agree with direct
recovery followed by the categorical tower comparison, as full DR morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open OneGonSmoothing CharacterSchemeBaseChange GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (t : A) (ht : IsUnit (1 + 432 * t))

/-- Successively apply the actual arithmetic coefficient comparisons. -/
irreducible_def iteratedCoefficientIso :
    curve (algebraMap A C t) (coefficientParameter_isUnit t ht) ≅
      ((curve t ht).baseChange (baseMap A B)).baseChange (baseMap B C) :=
  parameterIso (IsScalarTower.algebraMap_apply A B C t)
    (coefficientParameter_isUnit t ht)
    (coefficientParameter_isUnit (S := C) _ (coefficientParameter_isUnit (S := B) t ht)) ≪≫
      coefficientIso (S := C) (algebraMap A B t) (coefficientParameter_isUnit t ht) ≪≫
        (baseChangeFunctor (baseMap B C)).mapIso (coefficientIso (S := B) t ht)

/-- Iterated recovery retains the direct original whole-cubic projection. -/
@[reassoc] theorem iteratedCoefficientIso_fst_fst :
    (iteratedCoefficientIso A B C t ht).hom.curve.left ≫
      pullback.fst ((curve t ht).baseChange (baseMap A B)).curve.hom (baseMap B C) ≫
        pullback.fst (family t).hom (baseMap A B) = coefficientMorphism (S := C) t := by
  let hb := coefficientParameter_isUnit (S := B) t ht
  have hbc : (coefficientIso (S := C) (algebraMap A B t) hb).hom.curve.left ≫
      pullback.fst (curve (algebraMap A B t) hb).curve.hom (baseMap B C) =
        coefficientMorphism (S := C) (algebraMap A B t) := coefficientIso_curve_fst _ _
  rw [iteratedCoefficientIso_def]
  change (_ ≫ _ ≫ ((Over.pullback (baseMap B C)).map
    (coefficientIso (S := B) t ht).hom.curve).left) ≫ _ ≫ _ = _
  simp only [Over.pullback_map_left, Category.assoc]
  erw [pullback.lift_fst_assoc]
  simp only [Category.assoc]
  erw [coefficientIso_curve_fst (S := B) t ht]
  rw [← Category.assoc (coefficientIso (S := C) (algebraMap A B t) hb).hom.curve.left, hbc]
  rw [parameterIso_curve]
  exact coefficientMorphism_tower A B C t

/-- Direct and successive coefficient recovery agree in the full generalized-curve category. -/
theorem coefficientIso_tower :
    (iteratedCoefficientIso A B C t ht).hom =
      (coefficientIso (S := C) t ht).hom ≫
        ((curve t ht).baseChangeCompEqIso (baseMap A B) (baseMap B C) (baseMap A C)
          (coefficientTower_baseMap A B C).symm).hom := by
  apply forgetCurve.map_injective
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [iteratedCoefficientIso_fst_fst]
      change _ = (_ ≫ _) ≫ _ ≫ _
      rw [Category.assoc, baseChangeCompEqIso_curve_fst]
      exact (coefficientIso_curve_fst (S := C) t ht).symm
    · simp only [Category.assoc]
      change _ ≫ pullback.fst (pullback.snd (family t).hom (baseMap A B)) (baseMap B C) ≫
        pullback.snd (family t).hom (baseMap A B) =
          _ ≫ pullback.fst (pullback.snd (family t).hom (baseMap A B)) (baseMap B C) ≫
            pullback.snd (family t).hom (baseMap A B)
      rw [pullback.condition, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun k => k ≫ baseMap B C)
        ((Over.w _).trans (Over.w _).symm)
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
