/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXAlgebra

/-!
# Coordinate evaluation through individual coefficient casts

These lemmas evaluate the original incidence and slope coordinates through
one coefficient cast of an algebra equivalence. The equality of equivalence
types is arbitrary, so they apply to the proof terms produced by rewriting
coefficients in existing definitions. They neither construct a replacement
coordinate map nor identify the original residue comparison with a new map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

/-- Casting the scale preserves evaluation of the incidence coordinate. -/
theorem castScaleEquiv_t {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (W : WeierstrassCurve R) (s s' b3 b4 c : R) (hs : s = s')
    (hE : (Coordinate W s b3 b4 c ≃ₐ[R] B) = (Coordinate W s' b3 b4 c ≃ₐ[R] B))
    (e : Coordinate W s' b3 b4 c ≃ₐ[R] B) :
    (Eq.mpr hE e) (t W s b3 b4 c) = e (t W s' b3 b4 c) := by
  subst s'
  rfl

/-- Casting the divided linear slope coefficient preserves incidence evaluation. -/
theorem castB3Equiv_t {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (W : WeierstrassCurve R) (s b3 b3' b4 c : R) (h3 : b3 = b3')
    (hE : (Coordinate W s b3 b4 c ≃ₐ[R] B) = (Coordinate W s b3' b4 c ≃ₐ[R] B))
    (e : Coordinate W s b3' b4 c ≃ₐ[R] B) :
    (Eq.mpr hE e) (t W s b3 b4 c) = e (t W s b3' b4 c) := by
  subst b3'
  rfl

/-- Casting the divided horizontal coefficient preserves incidence evaluation. -/
theorem castB4Equiv_t {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (W : WeierstrassCurve R) (s b3 b4 b4' c : R) (h4 : b4 = b4')
    (hE : (Coordinate W s b3 b4 c ≃ₐ[R] B) = (Coordinate W s b3 b4' c ≃ₐ[R] B))
    (e : Coordinate W s b3 b4' c ≃ₐ[R] B) :
    (Eq.mpr hE e) (t W s b3 b4 c) = e (t W s b3 b4' c) := by
  subst b4'
  rfl

/-- Casting the scale preserves evaluation of the original slope. -/
theorem castScaleEquiv_v {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (W : WeierstrassCurve R) (s s' b3 b4 c : R) (hs : s = s')
    (hE : (Coordinate W s b3 b4 c ≃ₐ[R] B) = (Coordinate W s' b3 b4 c ≃ₐ[R] B))
    (e : Coordinate W s' b3 b4 c ≃ₐ[R] B) :
    (Eq.mpr hE e) (v W s b3 b4 c) = e (v W s' b3 b4 c) := by
  subst s'
  rfl

/-- Casting the divided linear slope coefficient preserves slope evaluation. -/
theorem castB3Equiv_v {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (W : WeierstrassCurve R) (s b3 b3' b4 c : R) (h3 : b3 = b3')
    (hE : (Coordinate W s b3 b4 c ≃ₐ[R] B) = (Coordinate W s b3' b4 c ≃ₐ[R] B))
    (e : Coordinate W s b3' b4 c ≃ₐ[R] B) :
    (Eq.mpr hE e) (v W s b3 b4 c) = e (v W s b3' b4 c) := by
  subst b3'
  rfl

/-- Casting the divided horizontal coefficient preserves slope evaluation. -/
theorem castB4Equiv_v {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (W : WeierstrassCurve R) (s b3 b4 b4' c : R) (h4 : b4 = b4')
    (hE : (Coordinate W s b3 b4 c ≃ₐ[R] B) = (Coordinate W s b3 b4' c ≃ₐ[R] B))
    (e : Coordinate W s b3 b4' c ≃ₐ[R] B) :
    (Eq.mpr hE e) (v W s b3 b4 c) = e (v W s b3 b4' c) := by
  subst b4'
  rfl

/-- Three successive coefficient casts preserve the original incidence evaluation. -/
theorem castZeroCoefficientsEquiv_t {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (W : WeierstrassCurve R) (s b3 b4 c : R) (hs : s = 0) (h3 : b3 = 0) (h4 : b4 = 0)
    (H1 : (Coordinate W s b3 b4 c ≃ₐ[R] B) = (Coordinate W 0 b3 b4 c ≃ₐ[R] B))
    (H2 : (Coordinate W 0 b3 b4 c ≃ₐ[R] B) = (Coordinate W 0 0 b4 c ≃ₐ[R] B))
    (H3 : (Coordinate W 0 0 b4 c ≃ₐ[R] B) = (Coordinate W 0 0 0 c ≃ₐ[R] B))
    (e : Coordinate W 0 0 0 c ≃ₐ[R] B) :
    (Eq.mpr H1 (Eq.mpr H2 (Eq.mpr H3 e))) (t W s b3 b4 c) = e (t W 0 0 0 c) := by
  subst s; subst b3; subst b4
  rfl

/-- Three successive coefficient casts preserve the original slope evaluation. -/
theorem castZeroCoefficientsEquiv_v {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (W : WeierstrassCurve R) (s b3 b4 c : R) (hs : s = 0) (h3 : b3 = 0) (h4 : b4 = 0)
    (H1 : (Coordinate W s b3 b4 c ≃ₐ[R] B) = (Coordinate W 0 b3 b4 c ≃ₐ[R] B))
    (H2 : (Coordinate W 0 b3 b4 c ≃ₐ[R] B) = (Coordinate W 0 0 b4 c ≃ₐ[R] B))
    (H3 : (Coordinate W 0 0 b4 c ≃ₐ[R] B) = (Coordinate W 0 0 0 c ≃ₐ[R] B))
    (e : Coordinate W 0 0 0 c ≃ₐ[R] B) :
    (Eq.mpr H1 (Eq.mpr H2 (Eq.mpr H3 e))) (v W s b3 b4 c) = e (v W 0 0 0 c) := by
  subst s; subst b3; subst b4
  rfl

end FLT.Mazur.WeierstrassModificationX
