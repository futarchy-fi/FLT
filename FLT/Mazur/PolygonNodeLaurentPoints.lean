/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberNodeComparison
public import FLT.Mazur.PolygonNodeBranches
public import FLT.Mazur.LaurentUnitPoints

/-!
# Laurent coordinates of points on the two actual node branches

A map from the node algebra is determined by its two tangent values.
When one is a unit, the whole spectrum map factors through the corresponding
original punctured branch, with that unit as its Laurent parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonNodeLaurentPoints
open PolygonNodeEqualizer PolygonNodeLocalization
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Both tangent values determine every function on the node. -/
theorem hom_ext (f g : A (R := R) →ₐ[R] S) (hx : f x = g x) (hy : f y = g y) :
    f = g := by
  have h : f.comp NodalFiber.polygonNodeEquiv.toAlgHom =
      g.comp NodalFiber.polygonNodeEquiv.toAlgHom := by
    apply NodalFiber.hom_ext
    · simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        NodalFiber.polygonNodeEquiv_p] using hx
    · simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        NodalFiber.polygonNodeEquiv_q] using hy
  apply AlgHom.ext
  intro z
  obtain ⟨w, rfl⟩ := NodalFiber.polygonNodeEquiv.surjective z
  exact congrArg (fun f => f w) h

/-- Restrict node functions to the first Laurent branch over the same coefficients. -/
def leftAlgebra : A (R := R) →ₐ[R] R[T;T⁻¹] :=
  { leftMap with commutes' := fun r => Polynomial.toLaurent_C r }

/-- Restrict node functions to the second Laurent branch over the same coefficients. -/
def rightAlgebra : A (R := R) →ₐ[R] R[T;T⁻¹] :=
  { rightMap with commutes' := fun r => Polynomial.toLaurent_C r }

/-- The first Laurent point has tangent values given by the unit and zero. -/
theorem left_evaluation (q : Sˣ) :
    (LaurentUnitPoints.evalUnit (R := R) q).comp leftAlgebra =
      PolygonNodeEvaluation.evaluation (q : S) 0 (mul_zero _) := by
  apply hom_ext
  · change LaurentUnitPoints.evalUnit q (leftMap x) = _
    rw [leftMap_x, LaurentUnitPoints.evalUnit_T, zpow_one,
      PolygonNodeEvaluation.evaluation_x]
  · change LaurentUnitPoints.evalUnit q (leftMap y) = _
    rw [leftMap_y, map_zero, PolygonNodeEvaluation.evaluation_y]

/-- The second Laurent point has tangent values zero and the prescribed unit. -/
theorem right_evaluation (q : Sˣ) :
    (LaurentUnitPoints.evalUnit (R := R) q).comp rightAlgebra =
      PolygonNodeEvaluation.evaluation 0 (q : S) (zero_mul _) := by
  apply hom_ext
  · change LaurentUnitPoints.evalUnit q (rightMap x) = _
    rw [rightMap_x, map_zero, PolygonNodeEvaluation.evaluation_x]
  · change LaurentUnitPoints.evalUnit q (rightMap y) = _
    rw [rightMap_y, LaurentUnitPoints.evalUnit_T, zpow_one,
      PolygonNodeEvaluation.evaluation_y]

/-- A unit first tangent value determines the entire point on the first branch. -/
theorem eq_left_evaluation (f : A (R := R) →ₐ[R] S) (q : Sˣ) (hx : f x = q) :
    f = (LaurentUnitPoints.evalUnit (R := R) q).comp leftAlgebra := by
  have hy : f y = 0 := by
    apply (Units.isUnit q).mul_left_cancel
    rw [← hx, ← map_mul, x_mul_y, map_zero, mul_zero]
  rw [left_evaluation]
  apply hom_ext
  · exact hx.trans (PolygonNodeEvaluation.evaluation_x _ _ _).symm
  · exact hy.trans (PolygonNodeEvaluation.evaluation_y _ _ _).symm

/-- A unit second tangent value determines the entire point on the second branch. -/
theorem eq_right_evaluation (f : A (R := R) →ₐ[R] S) (q : Sˣ) (hy : f y = q) :
    f = (LaurentUnitPoints.evalUnit (R := R) q).comp rightAlgebra := by
  have hx : f x = 0 := by
    apply (Units.isUnit q).mul_right_cancel
    rw [← hy, ← map_mul, x_mul_y, map_zero, zero_mul]
  rw [right_evaluation]
  apply hom_ext
  · exact hx.trans (PolygonNodeEvaluation.evaluation_x _ _ _).symm
  · exact hy.trans (PolygonNodeEvaluation.evaluation_y _ _ _).symm

/-- The original spectrum map factors through the first punctured branch. -/
theorem spec_left (f : A (R := R) →ₐ[R] S) (q : Sˣ) (hx : f x = q) :
    Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) q).toRingHom) ≫
        PolygonNodeBranches.left R := by
  rw [eq_left_evaluation f q hx]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The original spectrum map factors through the second punctured branch. -/
theorem spec_right (f : A (R := R) →ₐ[R] S) (q : Sˣ) (hy : f y = q) :
    Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) q).toRingHom) ≫
        PolygonNodeBranches.right R := by
  rw [eq_right_evaluation f q hy]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.PolygonNodeLaurentPoints
