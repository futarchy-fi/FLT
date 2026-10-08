/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionOutputFamilies

/-!
# Input maps and scalar relations on ordinary addition charts

Package the two actual affine input maps. Their line, cubic and output formulas
remain valid after arbitrary algebra specialization, including nonreduced rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- First affine input of an ordinary chart. -/
def ordinaryInputLeft (b : Bool) : Coordinate W 2 →ₐ[R]
    additionChartRing W (ordinaryIndex b) :=
  (additionChartAlgRestriction W (ordinaryIndex b)).comp (productLeft W)

/-- Second affine input of an ordinary chart. -/
def ordinaryInputRight (b : Bool) : Coordinate W 2 →ₐ[R]
    additionChartRing W (ordinaryIndex b) :=
  (additionChartAlgRestriction W (ordinaryIndex b)).comp (productRight W)

variable (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)

/-- The specialized slope satisfies the line equation for the two actual inputs. -/
theorem ordinarySpecialization_line :
    f (ordinaryChartSlope W b) *
        (f (ordinaryInputLeft W b (coord W 2 0)) -
          f (ordinaryInputRight W b (coord W 2 0))) =
      f (ordinaryInputLeft W b (coord W 2 1)) -
        f (ordinaryInputRight W b (coord W 2 1)) := by
  simpa only [ordinaryInputLeft, ordinaryInputRight, AlgHom.comp_apply,
    productX₁, productX₂, productY₁, productY₂, secantDenominator,
    verticalSecantDenominator, map_sub, map_mul] using
    congrArg f (ordinaryChartSlope_line W b)

/-- The divided difference also survives arbitrary algebra specialization. -/
theorem ordinarySpecialization_cubic :
    let x₁ := f (ordinaryInputLeft W b (coord W 2 0))
    let x₂ := f (ordinaryInputRight W b (coord W 2 0))
    let y₁ := f (ordinaryInputLeft W b (coord W 2 1))
    let y₂ := f (ordinaryInputRight W b (coord W 2 1))
    let V := (W.map (algebraMap R S)).toAffine
    f (ordinaryChartSlope W b) * (y₁ + y₂ + V.a₁ * x₂ + V.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + V.a₂ * (x₁ + x₂) + V.a₄ - V.a₁ * y₁ := by
  simpa only [ordinaryInputLeft, ordinaryInputRight, AlgHom.comp_apply,
    productX₁, productX₂, productY₁, productY₂, tangentDenominator, tangentNumerator,
    map_sub, map_add, map_mul, map_pow,
    AlgHom.commutes, WeierstrassCurve.toAffine, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] using
      congrArg f (ordinaryChartSlope_cubic W b)

/-- The actual output coordinates are the specialized ordinary addition formula. -/
theorem ordinarySpecialization_coord (i : Fin 3) :
    let V := (W.map (algebraMap R S)).toAffine
    let x₁ := f (ordinaryInputLeft W b (coord W 2 0))
    let x₂ := f (ordinaryInputRight W b (coord W 2 0))
    let y₁ := f (ordinaryInputLeft W b (coord W 2 1))
    f (ordinaryChartAddition W b (coord W 2 i)) =
      ![V.addX x₁ x₂ (f (ordinaryChartSlope W b)),
        V.addY x₁ x₂ y₁ (f (ordinaryChartSlope W b)), 1] i :=
  ordinaryChartAddition_map_coord W b f i

/-- The x-coordinate difference is a unit on the actual outer secant chart. -/
theorem ordinarySpecialization_secant_unit
    (f : additionChartRing W (ordinaryIndex false) →ₐ[R] S) :
    IsUnit (f (ordinaryInputLeft W false (coord W 2 0)) -
      f (ordinaryInputRight W false (coord W 2 0))) := by
  simpa only [ordinaryInputLeft, ordinaryInputRight, AlgHom.comp_apply,
    productX₁, productX₂, Bool.false_eq_true, ite_false, secantDenominator, map_sub] using
    (ordinaryChartDenominator_isUnit W false).map f

end FLT.Mazur.WeierstrassIntegralChart
