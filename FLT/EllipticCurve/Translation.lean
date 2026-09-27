/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.FunctionField
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Translation of the generic point

The generic point and its translates provide substitutions on the function
field. Over an algebraically closed base, a nonconstant point has
transcendental x-coordinate.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.FunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The x-coordinate of the generic point in the fraction field. -/
noncomputable def genericX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing X)

/-- The y-coordinate of the generic point in the fraction field. -/
noncomputable def genericY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

/-- Polynomial evaluation at the generic x-coordinate is the canonical inclusion. -/
theorem aeval_genericX (p : F[X]) :
    aeval (genericX W) p =
      algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X]
    rfl

/-- The generic x-coordinate is transcendental over the ground field. -/
theorem genericX_transcendental : Transcendental F (genericX W) := by
  rw [transcendental_iff_injective]
  intro p q hpq
  rw [aeval_genericX, aeval_genericX] at hpq
  apply (AdjoinRoot.of.injective_of_degree_ne_zero
    (show W.polynomial.degree ≠ 0 by rw [degree_polynomial]; decide))
  exact (IsFractionRing.injective W.CoordinateRing W.FunctionField) hpq

/-- The generic coordinates satisfy the curve equation. -/
theorem generic_equation :
    (W.map (algebraMap F W.FunctionField)).Equation (genericX W) (genericY W) := by
  change (W.map (algebraMap F W.FunctionField)).polynomial.evalEval _ _ = 0
  rw [map_polynomial, ← eval₂_eval₂RingHom_apply]
  have he : eval₂RingHom (algebraMap F W.FunctionField) (genericX W) =
      (algebraMap W.CoordinateRing W.FunctionField).comp
        (algebraMap F[X] W.CoordinateRing) := by
    exact RingHom.ext (aeval_genericX W)
  rw [he, genericY, ← hom_eval₂]
  rw [AdjoinRoot.algebraMap_eq]
  change algebraMap W.CoordinateRing W.FunctionField
    (W.polynomial.eval₂ (AdjoinRoot.of _) (AdjoinRoot.root _)) = 0
  rw [AdjoinRoot.eval₂_root, map_zero]

/-- A homomorphism on the function field is determined by the generic coordinates. -/
theorem algHom_ext {L : Type*} [Field L] [Algebra F L]
    {φ ψ : W.FunctionField →ₐ[F] L}
    (hx : φ (genericX W) = ψ (genericX W)) (hy : φ (genericY W) = ψ (genericY W)) :
    φ = ψ := by
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := W.CoordinateRing)
  intro f
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
  change φ (algebraMap W.CoordinateRing W.FunctionField _) = ψ (algebraMap _ _ _)
  simp only [Algebra.smul_def, mul_one, map_add, map_mul]
  change φ (algebraMap _ _ (algebraMap F[X] _ p)) +
    φ (algebraMap _ _ (algebraMap F[X] _ q)) * φ (genericY W) =
    ψ (algebraMap _ _ (algebraMap F[X] _ p)) +
      ψ (algebraMap _ _ (algebraMap F[X] _ q)) * ψ (genericY W)
  simp only [← aeval_genericX, ← aeval_algHom_apply, hx, hy]

variable [W.IsElliptic]

/-- The generic point of an elliptic curve. -/
noncomputable def genericPoint : (W⁄W.FunctionField).Point := by
  letI : (W⁄W.FunctionField).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F W.FunctionField)).IsElliptic
  exact .some (genericX W) (genericY W) (equation_iff_nonsingular.mp (generic_equation W))

end WeierstrassCurve.Affine.FunctionField

namespace IsAlgebraic

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed F]

/-- An algebraic element over an algebraically closed field is a ground-field constant. -/
theorem exists_algebraMap_eq {x : L} (hx : IsAlgebraic F x) :
    ∃ c : F, algebraMap F L c = x := by
  have hd := IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hx.isIntegral)
  have he := minpoly.aeval F x
  rw [eq_X_add_C_of_degree_eq_one hd, (minpoly.monic hx.isIntegral).leadingCoeff,
    C_1, one_mul, aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at he
  exact ⟨-(minpoly F x).coeff 0, by rw [map_neg]; exact he.symm⟩

end IsAlgebraic

namespace WeierstrassCurve.Affine

variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {W : WeierstrassCurve.Affine F}

/-- A point with ground-field x-coordinate has algebraic y-coordinate. -/
theorem isAlgebraic_y_of_equation {c : F} {y : L}
    (h : (W.map (algebraMap F L)).Equation (algebraMap F L c) y) : IsAlgebraic F y := by
  let p : F[X] := C 1 * X ^ 2 + C (W.a₁ * c + W.a₃) * X +
    C (-(c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆))
  refine ⟨p, ?_, ?_⟩
  · have hd : p.degree = 2 := degree_quadratic one_ne_zero
    intro hp
    rw [hp, degree_zero] at hd
    contradiction
  · have he := (equation_iff _ _).mp h
    simp only [Affine.map, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at he
    dsimp [p]
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, map_one, one_mul, map_neg]
    linear_combination he

variable [IsAlgClosed F] [DecidableEq F] [DecidableEq L]

/-- Over an algebraically closed base, a point with algebraic x-coordinate
comes from a point over the base field. -/
theorem point_mem_range_of_isAlgebraic_x {x y : L}
    (h : (W⁄L).Nonsingular x y) (hx : IsAlgebraic F x) :
    Point.some x y h ∈ (Point.map (W' := W) (Algebra.ofId F L)).range := by
  obtain ⟨c, rfl⟩ := hx.exists_algebraMap_eq
  obtain ⟨d, rfl⟩ := (isAlgebraic_y_of_equation h.1).exists_algebraMap_eq
  refine ⟨Point.some c d ((W.map_nonsingular (algebraMap F L).injective c d).mp h), ?_⟩
  rfl

end WeierstrassCurve.Affine


namespace WeierstrassCurve.Affine.FunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
variable [W.IsElliptic] [DecidableEq W.FunctionField]

omit [DecidableEq F] in
/-- The image of the generic point determines a function-field homomorphism. -/
theorem algHom_ext_of_genericPoint {φ ψ : W.FunctionField →ₐ[F] W.FunctionField}
    (h : Point.map (W' := W) φ (genericPoint W) = Point.map (W' := W) ψ (genericPoint W)) :
    φ = ψ := by
  simp only [genericPoint, Point.map_some] at h
  exact algHom_ext W (Point.some.inj h).1 (Point.some.inj h).2

omit [W.IsElliptic] in
set_option backward.isDefEq.respectTransparency false in
/-- A ground-field algebra homomorphism fixes every ground-field point. -/
theorem map_basePoint (φ : W.FunctionField →ₐ[F] W.FunctionField) (Q : W.Point) :
    Point.map (W' := W) φ (Point.map (W' := W) (Algebra.ofId F W.FunctionField) Q) =
      Point.map (W' := W) (Algebra.ofId F W.FunctionField) Q := by
  rw [Point.map_map]
  have he : φ.comp (Algebra.ofId F W.FunctionField) = Algebra.ofId F W.FunctionField := by
    ext
  rw [he]

/-- The generic point does not come from a ground-field point. -/
theorem genericPoint_not_mem_range :
    genericPoint W ∉ (Point.map (W' := W) (Algebra.ofId F W.FunctionField)).range := by
  rintro ⟨Q, hQ⟩
  rcases Q with (_ | ⟨x, y, h⟩)
  · exact (Point.some_ne_zero _ hQ.symm)
  · have hx : algebraMap F W.FunctionField x = genericX W := (Point.some.inj hQ).1
    exact genericX_transcendental W (hx ▸ isAlgebraic_algebraMap x)

/-- Translating the generic point by a ground-field point remains nonconstant. -/
theorem genericPoint_add_not_mem_range (Q : W.Point) :
    genericPoint W + Point.map (W' := W) (Algebra.ofId F W.FunctionField) Q ∉
      (Point.map (W' := W) (Algebra.ofId F W.FunctionField)).range := by
  rintro ⟨R, hR⟩
  apply genericPoint_not_mem_range W
  refine ⟨R - (show (W⁄F).Point from Q), ?_⟩
  rw [map_sub, hR, add_sub_cancel_right]

variable [IsAlgClosed F]

/-- A translate of the generic point is affine and has transcendental x-coordinate. -/
theorem exists_translated_generic (Q : W.Point) :
    ∃ x y, ∃ h : (W⁄W.FunctionField).Nonsingular x y,
      Point.some x y h = genericPoint W +
        Point.map (W' := W) (Algebra.ofId F W.FunctionField) Q ∧ Transcendental F x := by
  have hn := genericPoint_add_not_mem_range W Q
  cases hp : genericPoint W + Point.map (W' := W) (Algebra.ofId F W.FunctionField) Q with
  | zero => exact False.elim (hn (hp ▸ AddSubgroup.zero_mem _))
  | some x y h =>
    refine ⟨x, y, h, rfl, ?_⟩
    intro hx
    apply hn
    rw [hp]
    exact point_mem_range_of_isAlgebraic_x h hx

/-- The x-coordinate of the generic point translated by `Q`. -/
noncomputable def translatedX (Q : W.Point) : W.FunctionField :=
  (exists_translated_generic W Q).choose

/-- The y-coordinate of the generic point translated by `Q`. -/
noncomputable def translatedY (Q : W.Point) : W.FunctionField :=
  (exists_translated_generic W Q).choose_spec.choose

/-- The translated coordinates form a nonsingular affine point. -/
theorem translated_nonsingular (Q : W.Point) :
    (W⁄W.FunctionField).Nonsingular (translatedX W Q) (translatedY W Q) :=
  (exists_translated_generic W Q).choose_spec.choose_spec.choose

/-- The chosen translated coordinates represent addition by `Q`. -/
theorem translated_point (Q : W.Point) :
    Point.some (translatedX W Q) (translatedY W Q) (translated_nonsingular W Q) =
      genericPoint W + Point.map (W' := W) (Algebra.ofId F W.FunctionField) Q :=
  (exists_translated_generic W Q).choose_spec.choose_spec.choose_spec.1

/-- Translation preserves transcendence of the generic x-coordinate. -/
theorem translatedX_transcendental (Q : W.Point) : Transcendental F (translatedX W Q) :=
  (exists_translated_generic W Q).choose_spec.choose_spec.choose_spec.2

/-- Pullback of rational functions by translation by a ground-field point. -/
noncomputable def translationPullback (Q : W.Point) : W.FunctionField →ₐ[F] W.FunctionField :=
  CoordinateRing.evalFunctionField (translated_nonsingular W Q).1 (translatedX_transcendental W Q)

set_option backward.isDefEq.respectTransparency false in
/-- Translation pullback sends the generic x-coordinate to the translated x-coordinate. -/
theorem translationPullback_genericX (Q : W.Point) :
    translationPullback W Q (genericX W) = translatedX W Q := by
  rw [translationPullback, genericX, CoordinateRing.evalFunctionField_algebraMap,
    CoordinateRing.evalAt_polynomial, aeval_X]

set_option backward.isDefEq.respectTransparency false in
/-- Translation pullback sends the generic y-coordinate to the translated y-coordinate. -/
theorem translationPullback_genericY (Q : W.Point) :
    translationPullback W Q (genericY W) = translatedY W Q := by
  rw [translationPullback, genericY, CoordinateRing.evalFunctionField_algebraMap,
    CoordinateRing.evalAt_Y]

/-- On points, translation pullback sends the generic point to its translate. -/
theorem translationPullback_genericPoint (Q : W.Point) :
    Point.map (W' := W) (translationPullback W Q) (genericPoint W) =
      genericPoint W + Point.map (W' := W) (Algebra.ofId F W.FunctionField) Q := by
  rw [genericPoint, Point.map_some]
  simp only [translationPullback_genericX, translationPullback_genericY]
  exact translated_point W Q

set_option backward.isDefEq.respectTransparency false in
/-- Pullback by the zero translation is the identity. -/
theorem translationPullback_zero : translationPullback W 0 = AlgHom.id F W.FunctionField := by
  apply algHom_ext_of_genericPoint W
  rw [translationPullback_genericPoint, map_zero, add_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Successive translation pullbacks correspond to addition of the translating points. -/
theorem translationPullback_add (Q R : W.Point) :
    (translationPullback W Q).comp (translationPullback W R) = translationPullback W (Q + R) := by
  apply algHom_ext_of_genericPoint W
  rw [← Point.map_map, translationPullback_genericPoint, map_add,
    translationPullback_genericPoint, map_basePoint, translationPullback_genericPoint,
    map_add, add_assoc]

end WeierstrassCurve.Affine.FunctionField
