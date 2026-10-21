/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCommonCoefficientIso
public import FLT.Mazur.ArithmeticOneGonCoefficientTower

/-!
# Parameter compatibility of arithmetic coefficient recovery

Coefficient recovery commutes with transport of the smoothing parameter.
This identifies recovered common-ring comparisons without a new equality premise.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open OneGonSmoothing GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {r t : R} (h : r = t) (hr : IsUnit (1 + 432 * r)) (ht : IsUnit (1 + 432 * t))

/-- Coefficient recovery respects equality of the actual smoothing parameters. -/
@[reassoc] theorem parameterIso_coefficientIso :
    (parameterIso (congrArg (algebraMap R S) h)
      (coefficientParameter_isUnit r hr) (coefficientParameter_isUnit t ht)).hom ≫
        (coefficientIso (S := S) t ht).hom =
      (coefficientIso (S := S) r hr).hom ≫
        (baseChangeFunctor (CharacterSchemeBaseChange.baseMap R S)).map
          (parameterIso h hr ht).hom := by
  subst t
  rw [parameterIso_def, parameterIso_def]
  simp only [Iso.refl_hom, Category.id_comp]
  rw [(baseChangeFunctor (CharacterSchemeBaseChange.baseMap R S)).map_id (curve r hr)]
  exact (Category.comp_id (coefficientIso (S := S) r hr).hom).symm

section Common
open CharacterSchemeBaseChange
variable (A B C D : Type) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A C] [Algebra B C] [Algebra C D] [Algebra A D] [Algebra B D]
  [IsScalarTower A C D] [IsScalarTower B C D]
  (a : A) (b : B) (ha : IsUnit (1 + 432 * a)) (hb : IsUnit (1 + 432 * b))
  (e : algebraMap A C a = algebraMap B C b)

include e in
/-- Equal common-ring parameters have equal images in the original coefficient ring. -/
theorem commonCoefficient_parameter_tower : algebraMap A D a = algebraMap B D b :=
  (IsScalarTower.algebraMap_apply A C D a).trans
    ((congrArg (algebraMap C D) e).trans (IsScalarTower.algebraMap_apply B C D b).symm)

/-- The common full-curve comparison is compatible with successive original recovery. -/
@[reassoc] theorem commonCoefficientIso_tower_recovery :
    (iteratedCoefficientIso A C D a ha).hom ≫
      (baseChangeFunctor (baseMap C D)).map (commonCoefficientIso a b ha hb e).hom =
    (parameterIso (commonCoefficient_parameter_tower A B C D a b e)
      (coefficientParameter_isUnit a ha) (coefficientParameter_isUnit b hb)).hom ≫
        (iteratedCoefficientIso B C D b hb).hom := by
  let F := baseChangeFunctor (baseMap C D)
  have hc := congrArg (fun f => F.map f) (commonCoefficientIso_recovery a b ha hb e)
  simp only [Functor.map_comp] at hc
  rw [iteratedCoefficientIso_def, iteratedCoefficientIso_def]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [hc]
  let ac := coefficientParameter_isUnit (S := C) a ha
  let bc := coefficientParameter_isUnit (S := C) b hb
  have hn := parameterIso_coefficientIso (S := D) e ac bc
  rw [← Category.assoc (coefficientIso (S := D) (algebraMap A C a) ac).hom,
    ← hn]
  simp only [Category.assoc]
  have hp :
      (parameterIso (IsScalarTower.algebraMap_apply A C D a)
        (coefficientParameter_isUnit a ha) (coefficientParameter_isUnit _ ac)).hom ≫
          (parameterIso (congrArg (algebraMap C D) e)
            (coefficientParameter_isUnit _ ac) (coefficientParameter_isUnit _ bc)).hom =
      (parameterIso (commonCoefficient_parameter_tower A B C D a b e)
        (coefficientParameter_isUnit a ha) (coefficientParameter_isUnit b hb)).hom ≫
          (parameterIso (IsScalarTower.algebraMap_apply B C D b)
            (coefficientParameter_isUnit b hb) (coefficientParameter_isUnit _ bc)).hom := by
    rw [parameterIso_trans, parameterIso_trans]
  rw [← Category.assoc, hp]
  simp only [Category.assoc, F]

end Common
end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
