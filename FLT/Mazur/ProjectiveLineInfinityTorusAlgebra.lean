/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTransportGeometry
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# The translated infinity torus

The right affine coordinate w=a⁻¹(T-1) identifies the Laurent torus with
the entire principal open 1+a*w. The equivalence retains all base functions.
-/

@[expose] public noncomputable section
open Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [CommRing K] (a : Kˣ)

/-- The function cutting out the translated infinity torus. -/
def infinityTorusPolynomial : K[X] := 1 + C (a : K) * X

/-- Change from the right affine coordinate to the translated torus coordinate. -/
def infinityTorusAffineEquiv : K[X] ≃ₐ[K] K[X] :=
  AlgEquiv.ofAlgHom (aeval (C (↑a⁻¹ : K) * (X - 1)))
    (aeval (infinityTorusPolynomial a))
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X, map_mul, aeval_C,
        map_one, infinityTorusPolynomial, map_add]
      simp [← mul_assoc, ← C_mul])
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X, infinityTorusPolynomial,
        map_mul, aeval_C]
      simp [← mul_assoc, ← C_mul])

/-- The affine substitution retains its exact normalization. -/
theorem infinityTorusAffineEquiv_X :
    infinityTorusAffineEquiv a X = C (↑a⁻¹ : K) * (X - 1) := aeval_X _

/-- The coordinate change fixes every coefficient. -/
theorem infinityTorusAffineEquiv_C (r : K) :
    infinityTorusAffineEquiv a (C r) = C r := (infinityTorusAffineEquiv a).commutes r

/-- The inverted polynomial becomes the Laurent generator. -/
theorem infinityTorusAffineEquiv_polynomial :
    infinityTorusAffineEquiv a (infinityTorusPolynomial a) = X := by
  simp only [infinityTorusPolynomial, map_add, map_one, map_mul,
    infinityTorusAffineEquiv_C, infinityTorusAffineEquiv_X]
  simp [← mul_assoc, ← C_mul]

local instance infinityTorusLaurentTower : IsScalarTower K K[X] K[T;T⁻¹] :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (Polynomial.toLaurent_C x).symm)

/-- The full translated principal localization is the Laurent algebra. -/
def infinityTorusEquiv : Localization.Away (infinityTorusPolynomial a) ≃ₐ[K] K[T;T⁻¹] :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (infinityTorusPolynomial a)) (T := Submonoid.powers (X : K[X]))
    _ _ (infinityTorusAffineEquiv a) (by
      rw [Submonoid.map_powers, infinityTorusAffineEquiv_polynomial])

/-- The localization equivalence retains every original polynomial function. -/
theorem infinityTorusEquiv_base (p : K[X]) :
    infinityTorusEquiv a
      (algebraMap K[X] (Localization.Away (infinityTorusPolynomial a)) p) =
        Polynomial.toLaurent (infinityTorusAffineEquiv a p) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The inclusion in the right affine chart on coordinate rings. -/
def infinityTorusMap : K[X] →ₐ[K] K[T;T⁻¹] :=
  aeval (LaurentPolynomial.C (↑a⁻¹ : K) * (LaurentPolynomial.T 1 - 1))

/-- The right affine coordinate is precisely a⁻¹(T-1). -/
theorem infinityTorusMap_X : infinityTorusMap a X =
    LaurentPolynomial.C (↑a⁻¹ : K) * (LaurentPolynomial.T 1 - 1) := aeval_X _

/-- All functions agree with the localization presentation of the torus inclusion. -/
theorem infinityTorusEquiv_base_map (p : K[X]) :
    infinityTorusEquiv a
      (algebraMap K[X] (Localization.Away (infinityTorusPolynomial a)) p) =
        infinityTorusMap a p := by
  rw [infinityTorusEquiv_base]
  have h : Polynomial.toLaurent.comp (infinityTorusAffineEquiv a).toRingHom =
      (infinityTorusMap a).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      change Polynomial.toLaurent (infinityTorusAffineEquiv a (C r)) =
        infinityTorusMap a (C r)
      rw [infinityTorusAffineEquiv_C, Polynomial.toLaurent_C]
      exact ((infinityTorusMap a).commutes r).symm
    · change Polynomial.toLaurent (infinityTorusAffineEquiv a X) = infinityTorusMap a X
      rw [infinityTorusAffineEquiv_X, map_mul, map_sub, map_one,
        Polynomial.toLaurent_C, Polynomial.toLaurent_X, infinityTorusMap_X]
  exact RingHom.congr_fun h p

end FLT.Mazur.ProjectiveLine
