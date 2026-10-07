/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveComparison
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
/-! # Local Weierstrass coordinate changes

The homogeneous substitution preserves the Weierstrass cubic up to u^6
over every commutative coefficient ring. It gives an affine-chart map
and an infinity-chart map after inverting the transformed Y-coordinate.
A span identity proves that the affine overlap and this neighborhood
cover the infinity chart. Gluing these maps is a separate step.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- An admissible coordinate substitution scales the homogeneous cubic by u^6. -/
theorem variableChange_projective_identity (x y z : R) :
    eval ![(C.u : R) ^ 2 * x + C.r * z,
      (C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t * z, z]
      W.toProjective.polynomial =
      (C.u : R) ^ 6 * eval ![x, y, z] (C • W).toProjective.polynomial := by
  have hs (k : ℕ) (a : R) : (C.u : R) ^ k * ((C.u⁻¹ : Rˣ) ^ k : R) * a = a := by
    rw [← mul_pow, C.u.mul_inv, one_pow, one_mul]
  have h1 : (C.u : R) * (C • W).a₁ = W.a₁ + 2 * C.s := by
    simpa only [variableChange_a₁, pow_one, mul_assoc] using hs 1 (W.a₁ + 2 * C.s)
  have h2 : (C.u : R) ^ 2 * (C • W).a₂ =
      W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
    simpa only [variableChange_a₂, Units.val_pow_eq_pow_val, mul_assoc] using
      hs 2 (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
  have h3 : (C.u : R) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t := by
    simpa only [variableChange_a₃, Units.val_pow_eq_pow_val, mul_assoc] using
      hs 3 (W.a₃ + C.r * W.a₁ + 2 * C.t)
  have h4 : (C.u : R) ^ 4 * (C • W).a₄ =
      W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ +
        3 * C.r ^ 2 - 2 * C.s * C.t := by
    simpa only [variableChange_a₄, Units.val_pow_eq_pow_val, mul_assoc] using
      hs 4 (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ +
        3 * C.r ^ 2 - 2 * C.s * C.t)
  have h6 : (C.u : R) ^ 6 * (C • W).a₆ =
      W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ -
        C.t ^ 2 - C.r * C.t * W.a₁ := by
    simpa only [variableChange_a₆, Units.val_pow_eq_pow_val, mul_assoc] using
      hs 6 (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ -
        C.t ^ 2 - C.r * C.t * W.a₁)
  simp [Projective.polynomial]
  linear_combination
    -(C.u : R) ^ 5 * x * y * z * h1 +
      (C.u : R) ^ 4 * x ^ 2 * z * h2 -
      (C.u : R) ^ 3 * y * z ^ 2 * h3 +
      (C.u : R) ^ 2 * x * z ^ 2 * h4 + z ^ 3 * h6

/-- The affine coordinate substitution preserves the equation up to the unit u^6. -/
theorem variableChange_affine_identity (x y : R) :
    eval ![(C.u : R) ^ 2 * x + C.r,
      (C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t] (equation W false) =
      (C.u : R) ^ 6 * eval ![x, y] (equation (C • W) false) := by
  have h := variableChange_projective_identity W C x y 1
  simpa [equation, Projective.polynomial] using h

/-- Normalizing an invertible Y-coordinate scales the cubic by the cube of its inverse. -/
theorem projective_normalize_y (x y z t : R) (h : t * y = 1) :
    eval ![x * t, 1, z * t] W.toProjective.polynomial =
      t ^ 3 * eval ![x, y, z] W.toProjective.polynomial := by
  have he : ![x * t, 1, z * t] = ![t * x, t * y, t * z] := by
    ext i
    fin_cases i <;> simp [h, mul_comm]
  rw [he]
  simp [Projective.polynomial]
  ring

/-- The normalized infinity-coordinate substitution preserves the cubic equation. -/
theorem variableChange_infinity_identity (x z t : R)
    (ht : t * ((C.u : R) ^ 3 + (C.u : R) ^ 2 * C.s * x + C.t * z) = 1) :
    eval ![((C.u : R) ^ 2 * x + C.r * z) * t, z * t] (equation W true) =
      t ^ 3 * (C.u : R) ^ 6 * eval ![x, z] (equation (C • W) true) := by
  have hn := projective_normalize_y W ((C.u : R) ^ 2 * x + C.r * z)
    ((C.u : R) ^ 3 + (C.u : R) ^ 2 * C.s * x + C.t * z) z t ht
  have hp := variableChange_projective_identity W C x 1 z
  simp only [mul_one] at hp
  rw [hp] at hn
  simpa [equation, InfinityChart.equation, Projective.polynomial, mul_assoc] using hn

/-- The transformed ordinary affine coordinates. -/
def variableChangeAffineCoords : Fin 2 → Ring (C • W) false :=
  ![(algebraMap R _ (C.u : R)) ^ 2 * coord (C • W) false 0 + algebraMap R _ C.r,
    (algebraMap R _ (C.u : R)) ^ 3 * coord (C • W) false 1 +
      (algebraMap R _ (C.u : R)) ^ 2 * algebraMap R _ C.s * coord (C • W) false 0 +
      algebraMap R _ C.t]

/-- The transformed affine coordinates satisfy the target cubic equation. -/
theorem variableChangeAffineCoords_root :
    aeval (variableChangeAffineCoords W C) (equation W false) = 0 := by
  let B := Ring (C • W) false
  let f := algebraMap R B
  have h := variableChange_affine_identity (W.map f) (C.map f)
    (coord (C • W) false 0) (coord (C • W) false 1)
  rw [map_variableChange, ← map_equation W, ← map_equation (C • W)] at h
  simp only [eval_map] at h
  change aeval (variableChangeAffineCoords W C) (equation W false) =
    (f (C.u : R)) ^ 6 * aeval ![coord (C • W) false 0, coord (C • W) false 1]
      (equation (C • W) false) at h
  have hv : ![coord (C • W) false 0, coord (C • W) false 1] = coord (C • W) false := by
    ext i
    fin_cases i <;> rfl
  have he := eval₂_coord_equation (C • W) false (RingHom.id B)
  change aeval (coord (C • W) false) (equation (C • W) false) = 0 at he
  rw [hv, he, mul_zero] at h
  exact h

/-- The actual pullback of affine-chart functions along a coordinate change. -/
def variableChangeAffineMap : Ring W false →ₐ[R] Ring (C • W) false :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W false})
    (aeval (variableChangeAffineCoords W C)) (by
      change Ideal.span {equation W false} ≤
        RingHom.ker (aeval (variableChangeAffineCoords W C)).toRingHom
      rw [Ideal.span_le]
      rintro q (hq : q = equation W false)
      subst q
      exact variableChangeAffineCoords_root W C)

/-- The affine-chart pullback has the specified coordinate formulas. -/
@[simp] theorem variableChangeAffineMap_coord (i : Fin 2) :
    variableChangeAffineMap W C (coord W false i) = variableChangeAffineCoords W C i := by
  change aeval _ (MvPolynomial.X i) = _
  simp

/-- The coordinate change as a morphism of ordinary affine charts. -/
def variableChangeAffineMorphism : chart (C • W) false ⟶ chart W false :=
  Spec.map (CommRingCat.ofHom (variableChangeAffineMap W C).toRingHom)

/-- The affine coordinate change preserves the coefficient base. -/
theorem variableChangeAffineMorphism_toBase :
    variableChangeAffineMorphism W C ≫ chartToBase W false = chartToBase (C • W) false := by
  unfold variableChangeAffineMorphism chartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (variableChangeAffineMap W C).commutes

/-- The transformed homogeneous Y-coordinate on the source infinity chart. -/
def variableChangeInfinityDenominator : Ring (C • W) true :=
  (algebraMap R _ (C.u : R)) ^ 3 +
    (algebraMap R _ (C.u : R)) ^ 2 * algebraMap R _ C.s * coord (C • W) true 0 +
    algebraMap R _ C.t * coord (C • W) true 1

/-- The ordinary overlap and the transformed infinity neighborhood cover. -/
theorem variableChange_infinity_span :
    Ideal.span ({coord (C • W) true 1, variableChangeInfinityDenominator W C} :
      Set (Ring (C • W) true)) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let := hm
  let K := Ring (C • W) true ⧸ m
  let : Field K := Ideal.Quotient.field m
  let f : Ring (C • W) true →+* K := Ideal.Quotient.mk m
  have hz : f (coord (C • W) true 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hd : f (variableChangeInfinityDenominator W C) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have he := eval₂_coord_equation (C • W) (S := K) true f
  have hx : f (coord (C • W) true 0) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 3)
    simpa [equation, InfinityChart.equation, hz] using he
  have hu := ((C.u.isUnit.map (algebraMap R (Ring (C • W) true))).map f).ne_zero
  apply pow_ne_zero 3 hu
  simpa [variableChangeInfinityDenominator, hz, hx] using hd

/-- The source infinity chart localized at the transformed Y-coordinate. -/
abbrev VariableChangeNeighborhood := Localization.Away (variableChangeInfinityDenominator W C)

/-- The transformed coordinates normalized in the target infinity chart. -/
def variableChangeInfinityCoords : Fin 2 → VariableChangeNeighborhood W C :=
  ![((algebraMap R _ (C.u : R)) ^ 2 *
      algebraMap (Ring (C • W) true) _ (coord (C • W) true 0) +
      algebraMap R _ C.r * algebraMap (Ring (C • W) true) _ (coord (C • W) true 1)) *
        IsLocalization.Away.invSelf (variableChangeInfinityDenominator W C),
    algebraMap (Ring (C • W) true) _ (coord (C • W) true 1) *
      IsLocalization.Away.invSelf (variableChangeInfinityDenominator W C)]

/-- The normalized infinity coordinates satisfy the target cubic equation. -/
theorem variableChangeInfinityCoords_root :
    aeval (variableChangeInfinityCoords W C) (equation W true) = 0 := by
  let N := VariableChangeNeighborhood W C
  let f := algebraMap (Ring (C • W) true) N
  let t : N := IsLocalization.Away.invSelf (variableChangeInfinityDenominator W C)
  have ht : t * ((algebraMap R N (C.u : R)) ^ 3 +
      (algebraMap R N (C.u : R)) ^ 2 * algebraMap R N C.s * f (coord (C • W) true 0) +
      algebraMap R N C.t * f (coord (C • W) true 1)) = 1 := by
    have h : t * f (variableChangeInfinityDenominator W C) = 1 := by
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf (variableChangeInfinityDenominator W C)
    simpa only [f, variableChangeInfinityDenominator, map_add, map_pow, map_mul,
      ← IsScalarTower.algebraMap_apply R (Ring (C • W) true)] using h
  have h := variableChange_infinity_identity (W.map (algebraMap R N))
    (C.map (algebraMap R N)) (f (coord (C • W) true 0)) (f (coord (C • W) true 1)) t ht
  rw [map_variableChange, ← map_equation W, ← map_equation (C • W)] at h
  simp only [eval_map] at h
  have he := eval₂_coord_equation (C • W) (S := N) true f
  dsimp only [f] at he
  rw [← IsScalarTower.algebraMap_eq R (Ring (C • W) true) N] at he
  have hv : ![f (coord (C • W) true 0), f (coord (C • W) true 1)] =
      fun i => f (coord (C • W) true i) := by
    ext i
    fin_cases i <;> rfl
  rw [hv, he, mul_zero] at h
  exact h

/-- The actual pullback of infinity-chart functions on the regular neighborhood. -/
def variableChangeInfinityMap : Ring W true →ₐ[R] VariableChangeNeighborhood W C :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W true})
    (aeval (variableChangeInfinityCoords W C)) (by
      change Ideal.span {equation W true} ≤
        RingHom.ker (aeval (variableChangeInfinityCoords W C)).toRingHom
      rw [Ideal.span_le]
      rintro q (hq : q = equation W true)
      subst q
      exact variableChangeInfinityCoords_root W C)

/-- The infinity-chart pullback has the normalized coordinate formulas. -/
@[simp] theorem variableChangeInfinityMap_coord (i : Fin 2) :
    variableChangeInfinityMap W C (coord W true i) = variableChangeInfinityCoords W C i := by
  change aeval _ (MvPolynomial.X i) = _
  simp

/-- The coordinate change near infinity as an actual scheme morphism. -/
def variableChangeInfinityMorphism :
    Spec (.of (VariableChangeNeighborhood W C)) ⟶ chart W true :=
  Spec.map (CommRingCat.ofHom (variableChangeInfinityMap W C).toRingHom)

end WeierstrassCurve.CubicCharts
