/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFrameScaling
public import FLT.Mazur.GeneralizedCurveMarkingCoordinateRing
public import FLT.Mazur.WeierstrassEvaluatedEquationRigidity
public import FLT.Mazur.WeierstrassVariableChangeIntegralEquation

/-!
# The actual relative equations under marking-frame change

The transition unit constructs an admissible change of variables. Faithful
evaluation in the original complement function ring proves equality of the
complete equations, including all nilpotent and mixed-characteristic terms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

variable (e f : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "W" => smoothMarkingWeierstrassCurve E s e
local notation "V" => smoothMarkingWeierstrassCurve E s f
local notation "φ" => smoothMarkingComplementBaseMap E s

/-- The admissible change taking the e coordinates to the f coordinates. -/
def smoothMarkingFrameChange : VariableChange Γ(S, ⊤) :=
  ⟨smoothMarkingFrameUnit E s e f, 0, 0, 0⟩

/-- The original chart has a faithful evaluation on the actual marked-point complement. -/
def smoothMarkingChartRingEquiv : Coordinate (W) 2 ≃+*
    Γ(Scheme.Opens.toScheme (X := E.curve.left)
      (s ≫ E.inclusion).left.ker.support.compl, ⊤) :=
  (affineChartMonicEquiv (W)).toRingEquiv.trans (smoothMarkingCoordinateRingEquiv E s e)

/-- The chart equivalence retains the original coefficient map. -/
theorem smoothMarkingChartRingEquiv_scalar (a : Γ(S, ⊤)) :
    smoothMarkingChartRingEquiv E s e (algebraMap Γ(S, ⊤) _ a) = φ a := by
  change smoothMarkingCoordinateRingEquiv E s e
    (affineChartToMonic (W) (algebraMap Γ(S, ⊤) _ a)) = _
  rw [AlgHom.commutes, smoothMarkingCoordinateRingEquiv_scalar]

/-- The chart equivalence retains the original order-two coordinate. -/
theorem smoothMarkingChartRingEquiv_x :
    smoothMarkingChartRingEquiv E s e (coord (W) 2 0) =
      smoothMarkingComplementX E s e := by
  change smoothMarkingCoordinateRingEquiv E s e (affineChartToMonic (W) (coord (W) 2 0)) = _
  rw [affineChartToMonic, evaluation_coord]
  exact smoothMarkingCoordinateRingEquiv_x E s e

/-- The chart equivalence retains the original order-three coordinate. -/
theorem smoothMarkingChartRingEquiv_y :
    smoothMarkingChartRingEquiv E s e (coord (W) 2 1) =
      smoothMarkingComplementY E s e := by
  change smoothMarkingCoordinateRingEquiv E s e (affineChartToMonic (W) (coord (W) 2 1)) = _
  rw [affineChartToMonic, evaluation_coord]
  exact smoothMarkingCoordinateRingEquiv_y E s e

/-- The constructed admissible change identifies all five original cubic coefficients. -/
theorem smoothMarkingFrameChange_equation : smoothMarkingFrameChange E s e f • (V) = W := by
  apply affineEquation_curve_eq_of_injective (W) _ (φ)
    (smoothMarkingChartRingEquiv E s e).toRingHom
    (smoothMarkingChartRingEquiv E s e).injective
    (smoothMarkingChartRingEquiv_scalar E s e)
  change ((_ • (V)).map (φ)).toAffine.Equation
    (smoothMarkingChartRingEquiv E s e (coord (W) 2 0))
    (smoothMarkingChartRingEquiv E s e (coord (W) 2 1))
  rw [smoothMarkingChartRingEquiv_x, smoothMarkingChartRingEquiv_y, ← map_variableChange]
  apply (WeierstrassVariableChangeIntegralEquation.equation_iff _ _ _ _).mp
  have h := smoothMarkingWeierstrass_equation E s f
  rw [smoothMarkingComplementX_frameChange E s e f,
    smoothMarkingComplementY_frameChange E s e f] at h
  simpa only [smoothMarkingFrameChange, VariableChange.map, Units.coe_map,
    MonoidHom.coe_ofClass,
    map_zero, zero_mul, mul_zero, add_zero, ← map_pow] using h

end FLT.Mazur.GeneralizedEllipticCurve
