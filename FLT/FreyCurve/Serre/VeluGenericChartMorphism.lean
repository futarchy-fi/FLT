/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluFunctionField
public import FLT.Mazur.WeierstrassChartEvaluationComparison

/-!
# The original Vélu formulas define a generic cubic morphism

The actual rational functions determine a map from the source function field's
spectrum into the target cubic. Its chart coordinates and coefficient map are
retained. Extending it over the entire source curve is a separate construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The target affine chart evaluated at the original generic Vélu coordinates. -/
def veluGenericChart : Coordinate (curve E G) 2 →ₐ[K] FunctionField E :=
  evaluation (curve E G) 2
    ![liftX E (xFunction E G), liftY E (curve E G) (xFunction E G) (slopeFunction E G), 1]
    ((Projective.equation_some _ _).mpr (velu_lift_equation E G hodd)) rfl

/-- Its x coordinate is exactly the original rational x function. -/
@[simp] theorem veluGenericChart_x :
    veluGenericChart E G hodd (coord (curve E G) 2 0) = liftX E (xFunction E G) :=
  evaluation_coord _ _ _ _ _ _

/-- Its y coordinate is exactly the original lifted y function. -/
@[simp] theorem veluGenericChart_y :
    veluGenericChart E G hodd (coord (curve E G) 2 1) =
      liftY E (curve E G) (xFunction E G) (slopeFunction E G) :=
  evaluation_coord _ _ _ _ _ _

/-- The original formulas give a scheme morphism from the function field into the target cubic. -/
def veluGenericMorphism : Spec (.of (FunctionField E)) ⟶ integralCurve (curve E G) :=
  Spec.map (CommRingCat.ofHom (veluGenericChart E G hodd).toRingHom) ≫
    integralCurveChart (curve E G) 2

/-- The generic morphism is over the original coefficient field. -/
@[reassoc] theorem veluGenericMorphism_base :
    veluGenericMorphism E G hodd ≫ integralCurveStructure (curve E G) =
      Spec.map (CommRingCat.ofHom (algebraMap K (FunctionField E))) := by
  rw [veluGenericMorphism, Category.assoc, integralCurveChart_structure]
  exact specAlgHom_structure _

end WeierstrassCurve.Velu
