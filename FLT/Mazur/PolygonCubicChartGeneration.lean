/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicSections
/-!
# Cubic coordinate certificates at every normalization left-chart point

Two genuine polygon sections have component coordinates X and 1 + w X³.
They have no common zero at any prime of K[X], including non-rational points.
This is a coordinate certificate on normalization charts; descent to generation
of the polygon line and the projective chart construction remain separate.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)
/-- The prescribed cubic is the coordinate of the constructed polygon section. -/
lemma nodeSection_polynomial (v b c : Fin n → K) (i : Fin n) :
    ((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a v b c)).val i).val =
      (PolygonCubicInterpolation.cubic (v i) (b i) (c i)
        (weight K n a 3 i * v ((finRotate n).symm i))).val := by
  simp only [nodeSection, Equiv.apply_symm_apply, PolygonCubicInterpolation.lift]
/-- Constant node data give the component coordinate 1 + w X³. -/
lemma constantSection_polynomial (i : Fin n) :
    ((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a 1 0 0)).val i).val =
      1 + Polynomial.C (weight K n a 3 i) * Polynomial.X ^ 3 := by
  rw [nodeSection_polynomial]
  simp [PolygonCubicInterpolation.cubic, ← Polynomial.C_mul_X_pow_eq_monomial]
/-- Uniform first interior data give the component coordinate X. -/
lemma interiorSection_polynomial (i : Fin n) :
    ((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a 0 1 0)).val i).val =
      Polynomial.X := by
  rw [nodeSection_polynomial]
  simp [PolygonCubicInterpolation.cubic, ← Polynomial.C_mul_X_pow_eq_monomial]
/-- The two actual section coordinates do not vanish together at any prime. -/
lemma leftChart_no_common_zero (i : Fin n) (x : PrimeSpectrum K[X]) :
    ((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a 1 0 0)).val i).val
      ∉ x.asIdeal ∨
    ((sectionEquiv K n hn p q h a 2 (nodeSection K n hn p q h a 0 1 0)).val i).val
      ∉ x.asIdeal := by
  rw [constantSection_polynomial, interiorSection_polynomial]
  by_cases hx : Polynomial.X ∈ x.asIdeal
  · left
    intro hp
    have hm : Polynomial.C (weight K n a 3 i) * Polynomial.X ^ 3 ∈ x.asIdeal :=
      x.asIdeal.mul_mem_left _ (by
        rw [pow_succ]
        exact x.asIdeal.mul_mem_left _ hx)
    have hone : (1 : K[X]) ∈ x.asIdeal := by
      simpa only [add_sub_cancel_right] using x.asIdeal.sub_mem hp hm
    exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  · exact Or.inr hx
end FLT.Mazur.PolygonCubicSections
