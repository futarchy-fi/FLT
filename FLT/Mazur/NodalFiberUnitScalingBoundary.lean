/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberUnitScalingGeometry
public import FLT.Mazur.NodalFiberUnitScalingParameters
public import FLT.Mazur.PolygonSmoothingUnitBoundary

/-!
# Exact full puncture parameters after smoothing normalization

The corrected first Laurent parameter is the original first factor divided
by the smoothing unit. The opposite parameter is the original second factor.
Both factorizations are equalities of actual full scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (c t : R) (u : Rˣ) (hc : c = t * ↑u) (E : Coordinate c →ₐ[R] B)

/-- The actual first boundary unit, with the full inverse smoothing correction. -/
def unitNormalizedFirstUnit (hp : IsUnit (E (p c))) : Bˣ :=
  Units.map (algebraMap R B) u⁻¹ * hp.unit

/-- The corrected first unit retains the whole original first-factor function. -/
theorem unitNormalizedFirstUnit_coe (hp : IsUnit (E (p c))) :
    (unitNormalizedFirstUnit c u E hp : B) =
      algebraMap R B (↑u⁻¹ : R) * E (p c) := by
  simp only [unitNormalizedFirstUnit, Units.val_mul, Units.coe_map,
    MonoidHom.coe_ofClass, IsUnit.unit_spec]

/-- The original full first puncture factors through the exact normalized Laurent parameter. -/
@[reassoc] theorem unitSmoothingIso_first_boundary (hp : IsUnit (E (p c))) :
    Spec.map (CommRingCat.ofHom E.toRingHom) ≫ (unitSmoothingIso c t u hc).hom =
      Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := R) (unitNormalizedFirstUnit c u E hp)).toRingHom) ≫
          PolygonSmoothing.leftBranchOpen R t := by
  have h := PolygonSmoothing.boundary_leftBranchOpen t
    (unitNormalizedEvaluation c t u hc E) (unitNormalizedFirstUnit c u E hp) (by
      rw [unitNormalizedEvaluation_left, unitNormalizedFirstUnit_coe])
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact h

/-- The opposite full puncture keeps its original entire second-factor parameter. -/
@[reassoc] theorem unitSmoothingIso_second_boundary (hq : IsUnit (E (q c))) :
    Spec.map (CommRingCat.ofHom E.toRingHom) ≫ (unitSmoothingIso c t u hc).hom =
      Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := R) hq.unit).toRingHom) ≫
          PolygonSmoothing.rightBranchOpen R t := by
  have h := PolygonSmoothing.boundary_rightBranchOpen t
    (unitNormalizedEvaluation c t u hc E) hq.unit (by
      rw [unitNormalizedEvaluation_right, hq.unit_spec])
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact h

end FLT.Mazur.NodalFiber
