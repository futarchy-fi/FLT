/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonSmoothingMarking
public import FLT.Mazur.WeierstrassSplitNodalTorus
public import FLT.Mazur.WeierstrassVariableChangeZero

/-!
# The entire split nodal cubic is the original pinched one-gon

A unit scaling identifies the zero-parameter cubic with any split nodal
equation. Composing with the original pinching comparison includes the node
and preserves both the coefficient field and infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] (a : Kˣ)

/-- The admissible scaling from the fixed one-gon equation to the chosen tangent unit. -/
def splitNodalOneGonChange : VariableChange K := ⟨-a, 0, 0, 0⟩

/-- The scaling recovers exactly the zero-parameter equation, in every characteristic. -/
theorem splitNodalOneGonChange_equation :
    splitNodalOneGonChange a • splitNodalEquation a = OneGonSmoothing.equation 0 := by
  ext <;> simp [splitNodalOneGonChange, splitNodalEquation, OneGonSmoothing.equation,
    variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]

/-- The unit scaling is an isomorphism on the whole original projective cubic. -/
def splitNodalZeroCubicIso :
    integralCurve (OneGonSmoothing.equation (0 : K)) ≅ integralCurve (splitNodalEquation a) :=
  integralVariableChangeIso _ _ (splitNodalOneGonChange a) (splitNodalOneGonChange_equation a)

/-- The scaling retains the actual coefficient morphism. -/
@[reassoc] theorem splitNodalZeroCubicIso_structure :
    (splitNodalZeroCubicIso a).hom ≫ integralCurveStructure (splitNodalEquation a) =
      integralCurveStructure (OneGonSmoothing.equation (0 : K)) :=
  integralVariableChangeTo_structure _ _ _ _

/-- Infinity is preserved by the full cubic scaling. -/
@[reassoc] theorem splitNodalZeroCubicIso_zero :
    integralCurveZero (OneGonSmoothing.equation (0 : K)) ≫ (splitNodalZeroCubicIso a).hom =
      integralCurveZero (splitNodalEquation a) :=
  integralVariableChangeIso_zero _ _ _ _

/-- The full pinched one-gon, including its node, is the original split nodal cubic. -/
def splitNodalOneGonIso : OneGonGluing.scheme K ≅ integralCurve (splitNodalEquation a) :=
  OneGonSmoothing.zeroFiberIso K ≪≫ splitNodalZeroCubicIso a

/-- The global pinching comparison is over the unchanged coefficient field. -/
@[reassoc] theorem splitNodalOneGonIso_structure :
    (splitNodalOneGonIso a).hom ≫ integralCurveStructure (splitNodalEquation a) =
      OneGonGluing.toBase K := by
  rw [splitNodalOneGonIso, Iso.trans_hom, Category.assoc, splitNodalZeroCubicIso_structure]
  exact OneGonSmoothing.zeroFiberIso_structure K

/-- The original one-gon marking becomes the original cubic infinity. -/
@[reassoc] theorem splitNodalOneGonIso_marking (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) 1 i ≫
      (splitNodalOneGonIso a).hom = integralCurveZero (splitNodalEquation a) := by
  rw [splitNodalOneGonIso, Iso.trans_hom, ← Category.assoc,
    OneGonSmoothing.original_marking_zeroFiberIso]
  exact splitNodalZeroCubicIso_zero a

end FLT.Mazur.WeierstrassIntegralChart
