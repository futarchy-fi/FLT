/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicFieldAddition

/-! # Tangents and complete comparison with classical field-valued addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {K : Type u} [Field K] [Algebra R K]

/-- Evaluate the tangent localization where the divided-difference denominator is nonzero. -/
def tangentEvaluation (f g : Ring W false →ₐ[R] K)
    (h : chordDenominator (W.map (algebraMap R K))
      (g (coord W false 0)) (f (coord W false 1)) (g (coord W false 1)) ≠ 0) :
    TangentRing W →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom (tangentDenominator W)
    (f := Algebra.TensorProduct.productMap f g) (by
      have hd : Algebra.TensorProduct.productMap f g (tangentDenominator W) =
          chordDenominator (W.map (algebraMap R K))
            (g (coord W false 0)) (f (coord W false 1)) (g (coord W false 1)) := by
        simp [tangentDenominator, chordDenominator, WeierstrassCurve.map, pairCoord, pairInput]
      rw [hd]
      exact isUnit_iff_ne_zero.mpr h)

theorem tangentEvaluation_restrict (f g : Ring W false →ₐ[R] K)
    (h : chordDenominator (W.map (algebraMap R K))
      (g (coord W false 0)) (f (coord W false 1)) (g (coord W false 1)) ≠ 0)
    (x : AffinePairRing W) :
    tangentEvaluation W f g h (algebraMap (AffinePairRing W) (TangentRing W) x) =
      Algebra.TensorProduct.productMap f g x := by
  simp [tangentEvaluation, IsLocalization.Away.liftAlgHom_apply]

theorem tangentEvaluation_comp_restrict (f g : Ring W false →ₐ[R] K)
    (h : chordDenominator (W.map (algebraMap R K))
      (g (coord W false 0)) (f (coord W false 1)) (g (coord W false 1)) ≠ 0) :
    (tangentEvaluation W f g h).comp
      (IsScalarTower.toAlgHom R (AffinePairRing W) (TangentRing W)) =
        Algebra.TensorProduct.productMap f g := by
  apply AlgHom.ext
  intro x
  exact tangentEvaluation_restrict W f g h x

@[simp] theorem tangentEvaluation_coord (f g : Ring W false →ₐ[R] K)
    (h : chordDenominator (W.map (algebraMap R K))
      (g (coord W false 0)) (f (coord W false 1)) (g (coord W false 1)) ≠ 0)
    (b : Bool) (i : Fin 2) :
    tangentEvaluation W f g h (tangentCoord W b i) =
      (if b then g else f) (coord W false i) := by
  change tangentEvaluation W f g h
    (algebraMap (AffinePairRing W) (TangentRing W)
      ((if b then Algebra.TensorProduct.includeRight else Algebra.TensorProduct.includeLeft)
        (coord W false i))) = _
  rw [tangentEvaluation_restrict]
  cases b <;> simp

@[simp] theorem tangentEvaluation_inv (f g : Ring W false →ₐ[R] K)
    (h : chordDenominator (W.map (algebraMap R K))
      (g (coord W false 0)) (f (coord W false 1)) (g (coord W false 1)) ≠ 0) :
    tangentEvaluation W f g h (tangentInv W) =
      (chordDenominator (W.map (algebraMap R K))
        (g (coord W false 0)) (f (coord W false 1)) (g (coord W false 1)))⁻¹ := by
  have hh := congrArg (tangentEvaluation W f g h) (tangent_denominator_mul_inv W)
  simp only [chordDenominator, WeierstrassCurve.map, map_mul, map_add, map_one,
    AlgHom.commutes, tangentEvaluation_coord, Bool.false_eq_true, ↓reduceIte] at hh
  apply mul_left_cancel₀ h
  rw [mul_inv_cancel₀ h]
  exact hh

theorem affineAddition_after_tangent [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S] (f : TangentRing W →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom
        (f.comp (IsScalarTower.toAlgHom R (AffinePairRing W) (TangentRing W))).toRingHom) ≫
        affineAddition W =
      Spec.map (CommRingCat.ofHom (f.comp (tangentSum W)).toRingHom) ≫ affineChart W := by
  change Spec.map
      (CommRingCat.ofHom (algebraMap (AffinePairRing W) (TangentRing W)) ≫
        CommRingCat.ofHom f.toRingHom) ≫ affineAddition W = _
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    affineAdditionInclusion W 1 ≫ affineAddition W = _
  rw [affineAddition_restrict]
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ tangentAddition W = _
  unfold tangentAddition
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Doubling at a nonvertical tangent agrees with classical doubling. -/
theorem fieldPointPair_double_of_Y_ne [W.IsElliptic] [DecidableEq K]
    {x y : K} (hP : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (hy : y ≠ (W.map (algebraMap R K)).toAffine.negY x y) :
    fieldPointPair W (.some x y hP) (.some x y hP) ≫ addition W =
      fieldPointMorphism W (.some x y hP + .some x y hP) := by
  let E := (W.map (algebraMap R K)).toAffine
  let f := affineEvaluation W x y hP.1
  have hd : chordDenominator (W.map (algebraMap R K))
      (f (coord W false 0)) (f (coord W false 1)) (f (coord W false 1)) ≠ 0 := by
    simp only [f, affineEvaluation_coord, Matrix.cons_val_zero, Matrix.cons_val_one]
    intro he
    apply hy
    dsimp [chordDenominator, Affine.negY] at he ⊢
    linear_combination he
  let k := tangentEvaluation W f f hd
  have hk (b : Bool) (i : Fin 2) : k (tangentCoord W b i) = ![x, y] i := by
    cases b <;> simp [k, f]
  have hslope : k (tangentSlope W) = E.slope x x y y := by
    simp only [tangentSlope, chordNumerator, map_mul, map_sub, map_add, map_pow,
      AlgHom.commutes, WeierstrassCurve.map, hk]
    simp only [k, tangentEvaluation_inv, f, affineEvaluation_coord,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Affine.slope_of_Y_ne rfl hy]
    dsimp [chordDenominator, Affine.negY, E, WeierstrassCurve.map]
    field_simp
    ring
  have hn := Affine.nonsingular_add hP hP (fun h ↦ hy h.2)
  have hsum : k.comp (tangentSum W) =
      affineEvaluation W (E.addX x x (E.slope x x y y))
        (E.addY x x y (E.slope x x y y)) hn.1 := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change k (tangentSum W (coord W false i)) =
      affineEvaluation W (E.addX x x (E.slope x x y y))
        (E.addY x x y (E.slope x x y y)) hn.1 (coord W false i)
    rw [tangentSum_coord, affineEvaluation_coord]
    fin_cases i <;>
      simp [tangentSumCoords, Affine.addX, Affine.addY, Affine.negY, Affine.negAddY,
        WeierstrassCurve.map, hk, hslope, E]
  rw [fieldPointPair_some, chartPairEvaluation_addition, Affine.Point.add_of_Y_ne hy]
  change Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.productMap f f).toRingHom) ≫ affineAddition W =
      Spec.map (CommRingCat.ofHom
        (affineEvaluation W (E.addX x x (E.slope x x y y))
          (E.addY x x y (E.slope x x y y)) hn.1).toRingHom) ≫ affineChart W
  rw [← tangentEvaluation_comp_restrict W f f hd]
  exact (affineAddition_after_tangent W k).trans (by rw [hsum])

/-- On all classical field-valued points, the global morphism induces the established group law. -/
theorem fieldPointPair_add [W.IsElliptic] [DecidableEq K]
    (P Q : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointPair W P Q ≫ addition W = fieldPointMorphism W (P + Q) := by
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, zero_add, fieldPointPair_zero_left, Category.assoc,
      addition_zero_left, Category.comp_id]
  | some x y hP =>
    cases Q with
    | zero =>
      rw [← Affine.Point.zero_def, add_zero, fieldPointPair_zero_right, Category.assoc,
        addition_zero_right, Category.comp_id]
    | some z t hQ =>
      by_cases hx : x = z
      · subst z
        by_cases hy : y = (W.map (algebraMap R K)).toAffine.negY x t
        · have he : Affine.Point.some x t hQ = -Affine.Point.some x y hP := by
            rw [Affine.Point.neg_some]
            congr 1
            rw [hy, Affine.negY_negY]
          rw [he, fieldPointPair_inverse, Category.assoc, addition_inverse_right,
            fieldPointMorphism_toBase_assoc, add_neg_cancel]
          rfl
        · have ht : y = t := Affine.Y_eq_of_Y_ne hP.1 hQ.1 rfl hy
          subst t
          exact fieldPointPair_double_of_Y_ne W hP hy
      · exact fieldPointPair_add_of_X_ne W hP hQ hx

end WeierstrassCurve.CubicCharts
