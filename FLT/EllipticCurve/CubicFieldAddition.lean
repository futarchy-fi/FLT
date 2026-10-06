/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicFieldPoints

/-! # Compatibility with classical addition over fields -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {K : Type u} [Field K] [Algebra R K]

/-- Evaluate the secant localization at a pair with distinct horizontal coordinates. -/
def secantEvaluation (f g : Ring W false →ₐ[R] K)
    (h : f (coord W false 0) ≠ g (coord W false 0)) : SecantRing W →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom (secantDenominator W)
    (f := Algebra.TensorProduct.productMap f g) (by
      have hd : Algebra.TensorProduct.productMap f g (secantDenominator W) =
          g (coord W false 0) - f (coord W false 0) := by
        simp [secantDenominator]
      rw [hd]
      exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h.symm))

theorem secantEvaluation_restrict (f g : Ring W false →ₐ[R] K)
    (h : f (coord W false 0) ≠ g (coord W false 0)) (x : AffinePairRing W) :
    secantEvaluation W f g h (algebraMap (AffinePairRing W) (SecantRing W) x) =
      Algebra.TensorProduct.productMap f g x := by
  simp [secantEvaluation, IsLocalization.Away.liftAlgHom_apply]

theorem secantEvaluation_comp_restrict (f g : Ring W false →ₐ[R] K)
    (h : f (coord W false 0) ≠ g (coord W false 0)) :
    (secantEvaluation W f g h).comp
      (IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)) =
        Algebra.TensorProduct.productMap f g := by
  apply AlgHom.ext
  intro x
  exact secantEvaluation_restrict W f g h x

@[simp] theorem secantEvaluation_coord (f g : Ring W false →ₐ[R] K)
    (h : f (coord W false 0) ≠ g (coord W false 0)) (b : Bool) (i : Fin 2) :
    secantEvaluation W f g h (secantCoord W b i) =
      (if b then g else f) (coord W false i) := by
  change secantEvaluation W f g h
    (algebraMap (AffinePairRing W) (SecantRing W)
      ((if b then Algebra.TensorProduct.includeRight else Algebra.TensorProduct.includeLeft)
        (coord W false i))) = _
  rw [secantEvaluation_restrict]
  cases b <;> simp

@[simp] theorem secantEvaluation_inv (f g : Ring W false →ₐ[R] K)
    (h : f (coord W false 0) ≠ g (coord W false 0)) :
    secantEvaluation W f g h (secantInv W) =
      (g (coord W false 0) - f (coord W false 0))⁻¹ := by
  have hh := congrArg (secantEvaluation W f g h) (secant_difference_mul_inv W)
  simp only [map_mul, map_sub, map_one, secantEvaluation_coord, Bool.false_eq_true,
    ↓reduceIte] at hh
  apply (mul_left_cancel₀ (sub_ne_zero.mpr h.symm))
  rw [hh, mul_inv_cancel₀ (sub_ne_zero.mpr h.symm)]

/-- On a nonvertical secant, global scheme addition is the classical point addition. -/
theorem fieldPointPair_add_of_X_ne [W.IsElliptic] [DecidableEq K]
    {x y z t : K} (hP : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (hQ : (W.map (algebraMap R K)).toAffine.Nonsingular z t) (hx : x ≠ z) :
    fieldPointPair W (.some x y hP) (.some z t hQ) ≫ addition W =
      fieldPointMorphism W (.some x y hP + .some z t hQ) := by
  let E := (W.map (algebraMap R K)).toAffine
  let f := affineEvaluation W x y hP.1
  let g := affineEvaluation W z t hQ.1
  have hx' : f (coord W false 0) ≠ g (coord W false 0) := by
    simpa [f, g] using hx
  let k := secantEvaluation W f g hx'
  have hk (b : Bool) (i : Fin 2) :
      k (secantCoord W b i) = (if b then ![z, t] else ![x, y]) i := by
    cases b <;> simp [k, f, g]
  have hslope : k (secantSlope W) = E.slope x z y t := by
    simp only [secantSlope, map_mul, map_sub, hk]
    simp only [k, secantEvaluation_inv, f, g, affineEvaluation_coord,
      Matrix.cons_val_zero, Matrix.cons_val_one, Bool.false_eq_true, ↓reduceIte]
    rw [Affine.slope_of_X_ne hx]
    field_simp
    ring
  have hn := Affine.nonsingular_add hP hQ (fun h ↦ hx h.1)
  have hsum : k.comp (secantSum W) =
      affineEvaluation W (E.addX x z (E.slope x z y t))
        (E.addY x z y (E.slope x z y t)) hn.1 := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change k (secantSum W (coord W false i)) =
      affineEvaluation W (E.addX x z (E.slope x z y t))
        (E.addY x z y (E.slope x z y t)) hn.1 (coord W false i)
    rw [secantSum_coord, affineEvaluation_coord]
    fin_cases i <;>
      simp [secantSumCoords, Affine.addX, Affine.addY, Affine.negY, Affine.negAddY,
        WeierstrassCurve.map, hk, hslope, E]
  rw [fieldPointPair_some, chartPairEvaluation_addition, Affine.Point.add_of_X_ne hx]
  change Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.productMap f g).toRingHom) ≫ affineAddition W =
      Spec.map (CommRingCat.ofHom
        (affineEvaluation W (E.addX x z (E.slope x z y t))
          (E.addY x z y (E.slope x z y t)) hn.1).toRingHom) ≫ affineChart W
  rw [← secantEvaluation_comp_restrict W f g hx']
  exact (affineAddition_after_secant W k).trans (by rw [hsum])

end WeierstrassCurve.CubicCharts
