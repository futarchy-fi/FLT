/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCommonCoefficientCurve
public import FLT.Mazur.WeierstrassProperCoefficientComposition

/-!
# Composition of actual one-gon coefficient projections

The full proper coefficient projections compose along a scalar tower. The
equality between the direct and iterated parameters is retained explicitly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The original one-gon coefficient map retains its ambient projective coefficient map. -/
@[reassoc] theorem coefficientMorphism_projective {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] (t : A) :
    coefficientMorphism (S := B) t ≫ integralProjectiveMap (equation t) =
      integralProjectiveMap (equation (algebraMap A B t)) ≫
        ProjectiveSpace.coefficientMap (algebraMap A B) (Fin 3) :=
  properCoefficientMap_projective (equation t) (equation (algebraMap A B t))
    (algebraMap A B) (equation_map t (algebraMap A B)).symm

/-- Parameter transport retains the original whole-cubic projective inclusion. -/
@[reassoc] theorem parameterCurveIso_projective {A : Type} [CommRing A]
    {s t : A} (h : s = t) :
    (parameterCurveIso h).hom.left ≫ integralProjectiveMap (equation t) =
      integralProjectiveMap (equation s) := by
  subst t
  rw [parameterCurveIso_def]
  exact Category.id_comp _

variable (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (t : A)

/-- Iterated and direct whole-cubic projections agree after actual parameter transport. -/
@[reassoc] theorem coefficientMorphism_tower :
    (parameterCurveIso (IsScalarTower.algebraMap_apply A B C t)).hom.left ≫
      coefficientMorphism (S := C) (algebraMap A B t) ≫ coefficientMorphism (S := B) t =
        coefficientMorphism (S := C) t := by
  apply (cancel_mono (integralProjectiveMap (equation t))).mp
  rw [Category.assoc, Category.assoc, coefficientMorphism_projective,
    coefficientMorphism_projective_assoc, parameterCurveIso_projective_assoc,
    coefficientMorphism_projective, ProjectiveSpace.coefficientMap_comp]
  rw [← IsScalarTower.algebraMap_eq A B C]

end FLT.Mazur.OneGonSmoothing
