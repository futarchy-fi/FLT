/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentStageNormalForm

public import FLT.Mazur.ArithmeticOneGonCommonCoefficientIso

/-!
# Comparing independent generalized curves over their common finite ring

Both supplied smooth stages refine to the same literal coefficient subring.
Their full generalized curves compare by the proved arithmetic coefficient
isomorphisms and the equality of the actual smoothing parameters.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

/-- The literal left inclusion, supplied explicitly to avoid ambiguous instance search. -/
@[instance_reducible]
def commonLeftAlgebra : Algebra (base I t ht n s) (commonBase I t ht n s u i j) :=
  (Subalgebra.inclusion (base_le_common_left I t ht n s u i j)).toAlgebra

/-- The literal right inclusion into the same finite ring. -/
@[instance_reducible]
def commonRightAlgebra : Algebra (base I t ht n u) (commonBase I t ht n s u i j) :=
  (Subalgebra.inclusion (base_le_common_right I t ht n s u i j)).toAlgebra

/-- Normalize the common left model with its explicit coefficient inclusion. -/
theorem commonLeft_curve_eq :
    stageCurve I t ht n s (commonLeft I t ht n s u i j) hs =
      (ArithmeticOneGonGeneralizedCurve.curve (parameter I t ht n s)
        (parameter_complementaryUnit I t ht n s hs)).baseChange
          (@baseMap (base I t ht n s) (commonBase I t ht n s u i j) _ _
            (commonLeftAlgebra I t ht n s u i j)) := by
  exact stageCurve_eq I t ht n s (commonLeft I t ht n s u i j) hs

/-- Normalize the common right model with its explicit coefficient inclusion. -/
theorem commonRight_curve_eq :
    stageCurve I t ht n u (commonRight I t ht n s u i j) hu =
      (ArithmeticOneGonGeneralizedCurve.curve (parameter I t ht n u)
        (parameter_complementaryUnit I t ht n u hu)).baseChange
          (@baseMap (base I t ht n u) (commonBase I t ht n s u i j) _ _
            (commonRightAlgebra I t ht n s u i j)) := by
  exact stageCurve_eq I t ht n u (commonRight I t ht n s u i j) hu

/-- Compare the full independent models through their normalized arithmetic objects. -/
irreducible_def commonCurveIso :=
    @commonCoefficientIso (base I t ht n s) (base I t ht n u)
      (commonBase I t ht n s u i j) _ _ _
      (commonLeftAlgebra I t ht n s u i j) (commonRightAlgebra I t ht n s u i j)
      (parameter I t ht n s) (parameter I t ht n u)
      (parameter_complementaryUnit I t ht n s hs)
      (parameter_complementaryUnit I t ht n u hu)
      (common_parameter_eq I t ht n s u i j)

/-- The full comparison retains the original common whole-cubic comparison used for subgroups. -/
theorem commonCurveIso_curve :
    (commonCurveIso I t ht n s u i j hs hu).hom.curve =
      (@commonCoefficientCurveIso (base I t ht n s) (base I t ht n u)
        (commonBase I t ht n s u i j) _ _ _
        (commonLeftAlgebra I t ht n s u i j) (commonRightAlgebra I t ht n s u i j)
        (parameter I t ht n s) (parameter I t ht n u)
        (common_parameter_eq I t ht n s u i j)).hom := by
  rw [commonCurveIso_def]
  exact @commonCoefficientIso_curve (base I t ht n s) (base I t ht n u)
    (commonBase I t ht n s u i j) _ _ _
    (commonLeftAlgebra I t ht n s u i j) (commonRightAlgebra I t ht n s u i j) _ _ _ _ _

end FLT.Mazur.OneGonAdicIndependentModel
