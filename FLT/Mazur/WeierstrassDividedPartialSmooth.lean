/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPlanePresentation
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Both partial derivative opens of a divided chart are smooth

The actual plane presentation has one relation and two variables. Inverting
either partial gives a unit Jacobian, without inverting the chart scale.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6

/-- The two-variable presentation of the actual monic coordinate algebra. -/
def dividedPlanePresentation : Algebra.Presentation R A (Fin 2) Unit :=
  (Algebra.Presentation.naive (v := fun _ : Unit => planeEquation W s b3 b4 b6)).ofAlgEquiv
    (planeCoordinateEquiv W s b3 b4 b6).symm

/-- The presentation generators are exactly the original divided coordinates. -/
theorem dividedPlanePresentation_val :
    (dividedPlanePresentation W s b3 b4 b6).val = ![x W s b3 b4 b6, y W s b3 b4 b6] := by
  funext i
  exact fromPlaneCoordinate_mk W s b3 b4 b6 i

/-- An actual partial derivative, evaluated in the original coordinate algebra. -/
def dividedPartial (i : Fin 2) : A :=
  aeval ![x W s b3 b4 b6, y W s b3 b4 b6] (pderiv i (planeEquation W s b3 b4 b6))

/-- Choose either of the two variables for the single relation. -/
def dividedPreSubmersive (i : Fin 2) : Algebra.PreSubmersivePresentation R A (Fin 2) Unit where
  toPresentation := dividedPlanePresentation W s b3 b4 b6
  map := fun _ => i
  map_inj := Function.injective_of_subsingleton _

/-- The one-by-one Jacobian is the selected actual partial derivative. -/
theorem dividedPreSubmersive_jacobian (i : Fin 2) :
    (dividedPreSubmersive W s b3 b4 b6 i).jacobian = dividedPartial W s b3 b4 b6 i := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change aeval (dividedPlanePresentation W s b3 b4 b6).val
    (pderiv i (planeEquation W s b3 b4 b6)) = _
  rw [dividedPlanePresentation_val]
  rfl

/-- The derivative localization has an explicitly invertible Jacobian. -/
def dividedPartialSubmersive (i : Fin 2) : Algebra.SubmersivePresentation R
    (Localization.Away (dividedPartial W s b3 b4 b6 i)) (Unit ⊕ Fin 2) (Unit ⊕ Unit) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway
      (Localization.Away (dividedPartial W s b3 b4 b6 i))
        (dividedPartial W s b3 b4 b6 i)).comp (dividedPreSubmersive W s b3 b4 b6 i)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian,
      dividedPreSubmersive_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (dividedPartial W s b3 b4 b6 i)).mul
      (IsLocalization.Away.algebraMap_isUnit (dividedPartial W s b3 b4 b6 i))

/-- Both partial derivative opens are smooth over the original coefficient ring. -/
theorem dividedPartial_smooth (i : Fin 2) :
    Algebra.Smooth R (Localization.Away (dividedPartial W s b3 b4 b6 i)) := by
  let _ := (dividedPartialSubmersive W s b3 b4 b6 i).isStandardSmooth
  infer_instance

end FLT.Mazur.WeierstrassDilatation
