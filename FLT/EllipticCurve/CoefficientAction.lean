/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Multiplication
/-!
# Field automorphisms acting on elliptic rational functions

An automorphism of the coefficient extension fixing the field of definition
acts on regular and rational functions. It carries point ideals to mapped
point ideals and commutes with translation and multiplication pullbacks.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate WeierstrassCurve.Affine nonZeroDivisors
namespace WeierstrassCurve.Affine.FunctionField
/-- A function-field homomorphism is determined by constants and the two generic coordinates. -/
theorem ringHom_ext {F L : Type*} [Field F] [Field L] (W : Affine F)
    {φ ψ : W.FunctionField →+* L}
    (hc : ∀ c : F, φ (algebraMap F W.FunctionField c) =
      ψ (algebraMap F W.FunctionField c))
    (hx : φ (genericX W) = ψ (genericX W))
    (hy : φ (genericY W) = ψ (genericY W)) : φ = ψ := by
  have hp : φ.comp (algebraMap F[X] W.FunctionField) =
      ψ.comp (algebraMap F[X] W.FunctionField) := by
    apply Polynomial.ringHom_ext
    · intro c
      exact hc c
    · exact hx
  apply IsFractionRing.ringHom_ext (A := W.CoordinateRing)
  intro f
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
  change φ (algebraMap W.CoordinateRing W.FunctionField _) = ψ (algebraMap _ _ _)
  simp only [Algebra.smul_def, mul_one, map_add, map_mul]
  change φ (algebraMap F[X] W.FunctionField p) +
    φ (algebraMap F[X] W.FunctionField q) * φ (genericY W) =
    ψ (algebraMap F[X] W.FunctionField p) +
      ψ (algebraMap F[X] W.FunctionField q) * ψ (genericY W)
  have hp' (r : F[X]) := RingHom.congr_fun hp r
  simp only [RingHom.comp_apply] at hp'
  rw [hy, hp' p, hp' q]

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (E : Affine K)
  (σ : F ≃ₐ[K] F)
/-- Evaluate polynomials after applying the coefficient automorphism. -/
noncomputable def coefficientPolynomialHom : F[X] →ₐ[K] (E⁄F).FunctionField :=
  ((aeval (genericX (E⁄F))).restrictScalars K).comp (Polynomial.mapAlgHom σ.toAlgHom)
/-- The curve equation is fixed by automorphisms over its field of definition. -/
theorem coefficient_polynomial_fixed :
    (E⁄F).polynomial.map (Polynomial.mapRingHom σ.toRingHom) = (E⁄F).polynomial := by
  rw [← map_polynomial]
  congr 1
  ext <;> exact σ.commutes _
/-- Coefficient action on regular functions, with values in the function field. -/
noncomputable def coefficientCoordinateHom : (E⁄F).CoordinateRing →ₐ[K] (E⁄F).FunctionField :=
  AdjoinRoot.liftAlgHom (E⁄F).polynomial (coefficientPolynomialHom E σ)
    (genericY (E⁄F)) (by
      change (E⁄F).polynomial.eval₂
        ((aeval (genericX (E⁄F))).toRingHom.comp (Polynomial.mapRingHom σ.toRingHom))
          (genericY (E⁄F)) = 0
      rw [← eval₂_map, coefficient_polynomial_fixed]
      have hh := generic_equation (E⁄F)
      change ((E⁄F).map (algebraMap F (E⁄F).FunctionField)).polynomial.evalEval _ _ = 0 at hh
      rw [map_polynomial, ← eval₂_eval₂RingHom_apply] at hh
      exact hh)
/-- The coefficient action on polynomials is coefficientwise. -/
theorem coefficientCoordinateHom_polynomial (p : F[X]) :
    coefficientCoordinateHom E σ (algebraMap F[X] (E⁄F).CoordinateRing p) =
      aeval (genericX (E⁄F)) (p.map σ.toRingHom) := by
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ _
/-- The coefficient action on regular functions is injective. -/
theorem coefficientCoordinateHom_injective : Function.Injective (coefficientCoordinateHom E σ) := by
  apply CoordinateRing.injective_of_injective_polynomial
  intro p q he
  change coefficientCoordinateHom E σ (algebraMap F[X] (E⁄F).CoordinateRing p) =
    coefficientCoordinateHom E σ (algebraMap F[X] (E⁄F).CoordinateRing q) at he
  rw [coefficientCoordinateHom_polynomial, coefficientCoordinateHom_polynomial] at he
  exact Polynomial.map_injective σ.toRingHom σ.injective
    (transcendental_iff_injective.mp (genericX_transcendental (E⁄F)) he)
/-- The coefficient action extended to the rational function field. -/
noncomputable def coefficientHom : (E⁄F).FunctionField →ₐ[K] (E⁄F).FunctionField :=
  IsFractionRing.liftAlgHom (coefficientCoordinateHom_injective E σ)
/-- The rational action extends the action on regular functions. -/
theorem coefficientHom_algebraMap (f : (E⁄F).CoordinateRing) :
    coefficientHom E σ (algebraMap (E⁄F).CoordinateRing (E⁄F).FunctionField f) =
      coefficientCoordinateHom E σ f := by
  exact IsLocalization.lift_eq _ f

/-- The rational action restricts to the given automorphism on constants. -/
theorem coefficientHom_const (c : F) :
    coefficientHom E σ (algebraMap F (E⁄F).FunctionField c) =
      algebraMap F (E⁄F).FunctionField (σ c) := by
  change coefficientHom E σ (algebraMap (E⁄F).CoordinateRing _
    (algebraMap F[X] _ (C c))) = _
  rw [coefficientHom_algebraMap, coefficientCoordinateHom_polynomial, Polynomial.map_C, aeval_C]
  rfl
/-- The coefficient action fixes the generic x-coordinate. -/
theorem coefficientHom_genericX : coefficientHom E σ (genericX (E⁄F)) = genericX (E⁄F) := by
  rw [genericX, coefficientHom_algebraMap, coefficientCoordinateHom_polynomial,
    Polynomial.map_X, aeval_X]
  rfl
/-- The coefficient action fixes the generic y-coordinate. -/
theorem coefficientHom_genericY : coefficientHom E σ (genericY (E⁄F)) = genericY (E⁄F) := by
  rw [genericY, coefficientHom_algebraMap]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The coefficient action as an endomorphism of the coordinate ring. -/
noncomputable def coefficientCoordinate : (E⁄F).CoordinateRing →ₐ[K] (E⁄F).CoordinateRing :=
  AdjoinRoot.liftAlgHom (E⁄F).polynomial
    ((IsScalarTower.toAlgHom K F[X] (E⁄F).CoordinateRing).comp (Polynomial.mapAlgHom σ.toAlgHom))
    (CoordinateRing.mk (E⁄F) Y) (by
      change (E⁄F).polynomial.eval₂
        ((AdjoinRoot.of (E⁄F).polynomial).comp (Polynomial.mapRingHom σ.toRingHom))
        (AdjoinRoot.root (E⁄F).polynomial) = 0
      rw [← eval₂_map, coefficient_polynomial_fixed]
      exact AdjoinRoot.eval₂_root _)
/-- The regular action applies the automorphism to polynomial coefficients. -/
theorem coefficientCoordinate_polynomial (p : F[X]) :
    coefficientCoordinate E σ (algebraMap F[X] (E⁄F).CoordinateRing p) =
      algebraMap F[X] (E⁄F).CoordinateRing (p.map σ.toRingHom) := by
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ _
/-- The regular action fixes the y-coordinate. -/
theorem coefficientCoordinate_Y :
    coefficientCoordinate E σ (CoordinateRing.mk (E⁄F) Y) = CoordinateRing.mk (E⁄F) Y := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _
/-- The regular and rational coefficient actions agree. -/
theorem coefficientCoordinate_compat (f : (E⁄F).CoordinateRing) :
    algebraMap (E⁄F).CoordinateRing (E⁄F).FunctionField (coefficientCoordinate E σ f) =
      coefficientHom E σ (algebraMap (E⁄F).CoordinateRing (E⁄F).FunctionField f) := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
  simp only [Algebra.smul_def, map_add, map_mul, mul_one,
    coefficientCoordinate_polynomial, coefficientCoordinate_Y,
    coefficientHom_algebraMap, coefficientCoordinateHom_polynomial]
  congr 1
  · exact (aeval_genericX (E⁄F) _).symm
  · rw [← aeval_genericX]
    congr 1
    exact (AdjoinRoot.liftAlgHom_root _ _ _ _).symm
/-- The regular action restricts to the given automorphism on constants. -/
theorem coefficientCoordinate_const (c : F) :
    coefficientCoordinate E σ (algebraMap F (E⁄F).CoordinateRing c) =
      algebraMap F (E⁄F).CoordinateRing (σ c) := by
  change coefficientCoordinate E σ (algebraMap F[X] _ (C c)) = _
  rw [coefficientCoordinate_polynomial, Polynomial.map_C]
  rfl

/-- The coefficient action carries a point ideal to the ideal of the mapped point. -/
theorem coefficientCoordinate_XYIdeal (x y : F) :
    Ideal.map (coefficientCoordinate E σ).toRingHom (CoordinateRing.XYIdeal (E⁄F) x (C y)) =
      CoordinateRing.XYIdeal (E⁄F) (σ x) (C (σ y)) := by
  simp only [CoordinateRing.XYIdeal, Ideal.map_span, Set.image_pair]
  congr 1
  congr 1
  · change coefficientCoordinate E σ (algebraMap F[X] _ (X - C x)) = _
    rw [coefficientCoordinate_polynomial, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  · congr 1
    change coefficientCoordinate E σ
      (CoordinateRing.mk (E⁄F) Y - algebraMap F (E⁄F).CoordinateRing y) = _
    rw [map_sub, coefficientCoordinate_Y, coefficientCoordinate_const]
    rfl
variable [E.IsElliptic] [IsAlgClosed F] [DecidableEq F]
local instance : (E⁄F).IsElliptic :=
  inferInstanceAs (E.map (algebraMap K F)).IsElliptic
set_option backward.isDefEq.respectTransparency false
omit [IsAlgClosed F] [DecidableEq F] in
/-- The coefficient action fixes the generic point. -/
theorem coefficientHom_genericPoint :
    Point.map (W' := E) (coefficientHom E σ) (genericPoint (E⁄F)) = genericPoint (E⁄F) := by
  simp [genericPoint, Point.map, coefficientHom_genericX, coefficientHom_genericY]
omit [E.IsElliptic] [IsAlgClosed F] in
/-- The coefficient action carries a constant point to its mapped point. -/
theorem coefficientHom_basePoint (Q : (E⁄F).Point) :
    Point.map (W' := E) (coefficientHom E σ)
      (Point.map (W' := E⁄F) (Algebra.ofId F (E⁄F).FunctionField) Q) =
    Point.map (W' := E⁄F) (Algebra.ofId F (E⁄F).FunctionField)
      (Point.map (W' := E) σ.toAlgHom Q) := by
  cases Q with
  | zero => rfl
  | some x y h => simp [Point.map, coefficientHom_const]

/-- The coefficient action commutes with translation by the mapped point. -/
theorem coefficientHom_translation (Q : (E⁄F).Point) (f : (E⁄F).FunctionField) :
    coefficientHom E σ (translationPullback (E⁄F) Q f) =
      translationPullback (E⁄F) (Point.map (W' := E) σ.toAlgHom Q) (coefficientHom E σ f) := by
  have he := congrArg (Point.map (W' := E) (coefficientHom E σ))
    (translationPullback_genericPoint (E⁄F) Q)
  rw [map_add, coefficientHom_genericPoint, coefficientHom_basePoint] at he
  have hh : (coefficientHom E σ).comp ((translationPullback (E⁄F) Q).restrictScalars K) =
      ((translationPullback (E⁄F) (Point.map (W' := E) σ.toAlgHom Q)).restrictScalars K).comp
        (coefficientHom E σ) := by
    apply AlgHom.coe_ringHom_injective
    apply ringHom_ext (E⁄F)
    · intro c
      change coefficientHom E σ (translationPullback (E⁄F) Q (algebraMap F _ c)) =
        translationPullback (E⁄F) _ (coefficientHom E σ (algebraMap F _ c))
      rw [AlgHom.commutes, coefficientHom_const, AlgHom.commutes]
    · have hp := he.trans (translationPullback_genericPoint (E⁄F)
        (Point.map (W' := E) σ.toAlgHom Q)).symm
      simp only [genericPoint, Point.map_some] at hp
      change coefficientHom E σ (translationPullback (E⁄F) Q (genericX (E⁄F))) =
        translationPullback (E⁄F) _ (coefficientHom E σ (genericX (E⁄F)))
      rw [coefficientHom_genericX]
      exact (Point.some.inj hp).1
    · have hp := he.trans (translationPullback_genericPoint (E⁄F)
        (Point.map (W' := E) σ.toAlgHom Q)).symm
      simp only [genericPoint, Point.map_some] at hp
      change coefficientHom E σ (translationPullback (E⁄F) Q (genericY (E⁄F))) =
        translationPullback (E⁄F) _ (coefficientHom E σ (genericY (E⁄F)))
      rw [coefficientHom_genericY]
      exact (Point.some.inj hp).2
  exact congrArg (fun φ : (E⁄F).FunctionField →ₐ[K] (E⁄F).FunctionField => φ f) hh
omit [DecidableEq F] in
/-- The coefficient action commutes with multiplication pullback. -/
theorem coefficientHom_nsmulPullback (n : ℕ) (hn : n ≠ 0) (f : (E⁄F).FunctionField) :
    coefficientHom E σ (nsmulPullback (E⁄F) n hn f) =
      nsmulPullback (E⁄F) n hn (coefficientHom E σ f) := by
  have he := congrArg (Point.map (W' := E) (coefficientHom E σ))
    (nsmulPullback_genericPoint (E⁄F) n hn)
  rw [map_nsmul, coefficientHom_genericPoint] at he
  have hp := he.trans (nsmulPullback_genericPoint (E⁄F) n hn).symm
  simp only [genericPoint, Point.map_some] at hp
  have hh : (coefficientHom E σ).comp ((nsmulPullback (E⁄F) n hn).restrictScalars K) =
      ((nsmulPullback (E⁄F) n hn).restrictScalars K).comp (coefficientHom E σ) := by
    apply AlgHom.coe_ringHom_injective
    apply ringHom_ext (E⁄F)
    · intro c
      change coefficientHom E σ (nsmulPullback (E⁄F) n hn (algebraMap F _ c)) =
        nsmulPullback (E⁄F) n hn (coefficientHom E σ (algebraMap F _ c))
      rw [AlgHom.commutes, coefficientHom_const, AlgHom.commutes]
    · change coefficientHom E σ (nsmulPullback (E⁄F) n hn (genericX (E⁄F))) =
        nsmulPullback (E⁄F) n hn (coefficientHom E σ (genericX (E⁄F)))
      rw [coefficientHom_genericX]
      exact (Point.some.inj hp).1
    · change coefficientHom E σ (nsmulPullback (E⁄F) n hn (genericY (E⁄F))) =
        nsmulPullback (E⁄F) n hn (coefficientHom E σ (genericY (E⁄F)))
      rw [coefficientHom_genericY]
      exact (Point.some.inj hp).2
  exact congrArg (fun φ : (E⁄F).FunctionField →ₐ[K] (E⁄F).FunctionField => φ f) hh
end WeierstrassCurve.Affine.FunctionField
