/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupOverlapCoordinates
public import FLT.Mazur.EllipticSubgroupClosedFiberPoints

/-!
# Generic points agree across the subgroup closure gluing

Evaluation extends to the principal overlap whenever both primitive coordinates
are nonzero. The explicit transition identifies the two generic point morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The generic point morphism in one actual closure chart. -/
def genericChartPoint (P : Index A W H j) : Spec (.of K) ⟶ closureChart A W H j :=
  Spec.map (CommRingCat.ofHom (pointEvaluation A W H j P).toRingHom)

/-- The same evaluation on the principal overlap. -/
def genericOverlapEvaluation (P : OverlapIndex A W H j k) :
    LocalizedClosure A W H j k →ₐ[A] K :=
  IsLocalization.Away.liftAlgHom (closureCoord A W H j k)
    (show IsUnit (pointEvaluation A W H j P.1 (closureCoord A W H j k)) from
      isUnit_iff_ne_zero.mpr (by
        rw [closureCoord, pointEvaluation_coord]
        simpa only [coordinateMap_coord] using P.2))

/-- Overlap evaluation extends the original chart evaluation. -/
theorem genericOverlapEvaluation_algebraMap (P : OverlapIndex A W H j k)
    (x : Closure A W H j) :
    genericOverlapEvaluation A W H j k P
      (algebraMap (Closure A W H j) (LocalizedClosure A W H j k) x) =
        pointEvaluation A W H j P.1 x := by
  simp only [genericOverlapEvaluation, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The inverse overlap denominator evaluates to the reciprocal normalized coordinate. -/
theorem genericOverlapEvaluation_inverse (P : OverlapIndex A W H j k) :
    genericOverlapEvaluation A W H j k P
      (IsLocalization.Away.invSelf (closureCoord A W H j k)) =
        (coordinates A W H j P.1 k)⁻¹ := by
  have hk : coordinates A W H j P.1 k ≠ 0 := by
    simpa only [coordinateMap_coord] using P.2
  apply (mul_right_inj' hk).mp
  rw [mul_inv_cancel₀ hk]
  have he := congrArg (genericOverlapEvaluation A W H j k P)
    (IsLocalization.Away.mul_invSelf (S := LocalizedClosure A W H j k)
      (closureCoord A W H j k))
  rw [map_mul, genericOverlapEvaluation_algebraMap, map_one] at he
  change pointEvaluation A W H j P.1 (Ideal.Quotient.mk _ (coord W j k)) * _ = 1 at he
  rw [pointEvaluation_coord] at he
  exact he

/-- Renormalizing the overlap agrees with evaluating in the opposite chart. -/
theorem genericOverlapEvaluation_transition (P : OverlapIndex A W H j k) :
    (genericOverlapEvaluation A W H j k P).comp
      ((localizedClosureEquiv A W H j k).toAlgHom.comp
        (IsScalarTower.toAlgHom A (Closure A W H k) (LocalizedClosure A W H k j))) =
      pointEvaluation A W H k (overlapIndexSwap A W H j k P).1 := by
  apply Ideal.Quotient.algHom_ext
  apply hom_ext
  intro i
  change genericOverlapEvaluation A W H j k P
    (localizedClosureEquiv A W H j k (algebraMap (Closure A W H k)
      (LocalizedClosure A W H k j) (closureCoord A W H k i))) =
        pointEvaluation A W H k (overlapIndexSwap A W H j k P).1
          (Ideal.Quotient.mk _ (coord W k i))
  rw [localizedClosureEquiv_coord, map_mul, genericOverlapEvaluation_inverse,
    genericOverlapEvaluation_algebraMap, closureCoord, pointEvaluation_coord,
    pointEvaluation_coord, coordinates_swap]

set_option backward.isDefEq.respectTransparency false in
/-- The generic subgroup point has the same image in the glued scheme from either chart. -/
theorem genericChartPoint_overlap (P : OverlapIndex A W H j k) :
    genericChartPoint A W H j P.1 ≫ closureLeft A W H j k =
      genericChartPoint A W H k (overlapIndexSwap A W H j k P).1 ≫
        closureRight A W H j k := by
  let q := Spec.map (CommRingCat.ofHom (genericOverlapEvaluation A W H j k P).toRingHom)
  have hl : q ≫ closureToLeft A W H j k = genericChartPoint A W H j P.1 := by
    rw [closureToLeft, genericChartPoint, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (genericOverlapEvaluation_algebraMap A W H j k P)
  have hr : q ≫ closureToRight A W H j k =
      genericChartPoint A W H k (overlapIndexSwap A W H j k P).1 := by
    simp only [closureToRight, closureIntersectionIso, Functor.mapIso_hom, Iso.op_hom,
      RingEquiv.toCommRingCatIso_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
      closureToLeft, genericChartPoint, q, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (genericOverlapEvaluation_transition A W H j k P)
  rw [← hl, ← hr, Category.assoc, closure_overlap_condition, Category.assoc]

/-- An integral chart section extends the prescribed generic point morphism. -/
theorem genericChartPoint_integral (P : Index A W H j)
    (hj : IsUnit ((primitiveLift A W P.1.1).coords j)) :
    genericChartPoint A W H j P =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralChartPoint A W H j P.1 hj := by
  rw [genericChartPoint, integralChartPoint, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (pointEvaluation_integral A W H j P hj)

end FLT.Mazur.EllipticSubgroupChart
