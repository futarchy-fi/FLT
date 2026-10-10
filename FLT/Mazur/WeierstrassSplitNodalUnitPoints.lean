/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalPoints

/-!
# Units parametrize the actual split nodal points

Compose the proved Laurent chart equivalence with unit evaluation. The
resulting equivalence with classical nonsingular projective points agrees
with the constructed torus immersion into the original cubic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (a : Rˣ)

/-- Evaluate the original nodal chart at a unit through its Laurent coordinates. -/
def splitNodalUnitChart (t : Sˣ) : Coordinate (splitNodalEquation a) 1 →ₐ[R] S :=
  (LaurentUnitPoints.evalUnit t).comp (splitNodalChartToLaurent a)

/-- An arbitrary chart-valued point recovers its unit tangent coordinate. -/
def splitNodalChartUnit (f : Coordinate (splitNodalEquation a) 1 →ₐ[R] S) : Sˣ :=
  LaurentUnitPoints.pointUnit (f.comp (splitNodalLaurentToChart a))

/-- Recovering and then evaluating the unit recovers the actual algebra point. -/
@[simp] theorem splitNodalUnitChart_chartUnit
    (f : Coordinate (splitNodalEquation a) 1 →ₐ[R] S) :
    splitNodalUnitChart a (splitNodalChartUnit a f) = f := by
  rw [splitNodalUnitChart, splitNodalChartUnit, LaurentUnitPoints.evalUnit_pointUnit,
    AlgHom.comp_assoc, splitNodalLaurentToChart_comp, AlgHom.comp_id]

/-- Evaluating a unit and then recovering its tangent coordinate recovers that unit. -/
@[simp] theorem splitNodalChartUnit_unitChart (t : Sˣ) :
    splitNodalChartUnit a (splitNodalUnitChart a t) = t := by
  rw [splitNodalChartUnit, splitNodalUnitChart, AlgHom.comp_assoc,
    splitNodalChartToLaurent_comp, AlgHom.comp_id, LaurentUnitPoints.pointUnit_evalUnit]

/-- The actual nodal chart represents units over every coefficient algebra. -/
def splitNodalUnitChartEquiv : Sˣ ≃ (Coordinate (splitNodalEquation a) 1 →ₐ[R] S) where
  toFun := splitNodalUnitChart a
  invFun := splitNodalChartUnit a
  left_inv := splitNodalChartUnit_unitChart a
  right_inv := splitNodalUnitChart_chartUnit a

/-- Unit evaluation of the nodal chart commutes with every change of target algebra. -/
theorem splitNodalUnitChart_natural {T : Type u} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (t : Sˣ) :
    f.comp (splitNodalUnitChart a t) =
      splitNodalUnitChart a (Units.map f.toMonoidHom t) := by
  rw [splitNodalUnitChart, ← AlgHom.comp_assoc, LaurentUnitPoints.evalUnit_natural]
  rfl

/-- Unit one is the original normalized infinity evaluation, over every algebra. -/
theorem splitNodalUnitChart_one :
    splitNodalUnitChart (S := S) a 1 = chartInfinityEvaluation (splitNodalEquation a) := by
  apply hom_ext
  intro i
  fin_cases i <;> simp [splitNodalUnitChart, AlgHom.comp_apply,
    splitNodalLaurentX, splitNodalLaurentZ, chartInfinityEvaluation_coord]

variable {K : Type u} [Field K] [Algebra R K]

/-- Units are exactly the actual nonsingular projective points of the split nodal cubic. -/
def splitNodalUnitPointEquiv : Kˣ ≃
    ((splitNodalEquation a).map (algebraMap R K)).toProjective.Point :=
  (splitNodalUnitChartEquiv a).trans (splitNodalChartPointEquiv a)

/-- The explicit unit parametrization agrees with the original torus morphism on scheme points. -/
theorem splitNodalUnitPoint_toIntegral (t : Kˣ) :
    (projectiveToIntegral (splitNodalEquation a) (splitNodalUnitPointEquiv a t)).left =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) t).toRingHom) ≫
        splitNodalTorusToCurve a := by
  change (projectiveToIntegral _ (splitNodalChartProjective a (splitNodalUnitChart a t))).left = _
  rw [splitNodalChartProjective_toIntegral, splitNodalTorusToCurve, ← Category.assoc]
  change Spec.map (CommRingCat.ofHom (splitNodalUnitChart a t).toRingHom) ≫ _ =
    (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) t).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (splitNodalChartToLaurent a).toRingHom)) ≫ _
  rw [← Spec.map_comp]
  rfl

/-- The unit identity is the classical zero point as well as the scheme zero section. -/
@[simp] theorem splitNodalUnitPoint_one : splitNodalUnitPointEquiv (K := K) a 1 = 0 := by
  change splitNodalChartProjective a (splitNodalUnitChart a 1) = 0
  rw [splitNodalUnitChart_one]
  apply Point.ext
  change (⟦_⟧ : PointClass K) = ⟦![0, 1, 0]⟧
  congr 1
  funext i
  exact chartInfinityEvaluation_coord _ i

end FLT.Mazur.WeierstrassIntegralChart
