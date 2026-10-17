/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentNilpotentReparametrization
public import FLT.Mazur.LaurentScaledCoordinateIsomorphisms

/-!
# Weighted reductions of the full inverse Laurent substitution

An annihilator kills the complete coefficient-ideal error, including after
inversion of an algebra equivalence. This computes weighted inverse values
without expanding a constructed nilpotent inverse.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentWeightedInverse
open LaurentPolynomial PolygonScaledReciprocal
variable {R : Type*} [CommRing R]
local notation "L" => R[T;T⁻¹]

/-- A scalar annihilator removes any error in the extended principal coefficient ideal. -/
theorem weighted_eq_of_sub_mem (p e : R) (hep : e * p = 0) (x y : L)
    (h : x - y ∈ (Ideal.span {p}).map (algebraMap R L)) : C e * x = C e * y := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h
  obtain ⟨z, hz⟩ := h
  apply sub_eq_zero.mp
  rw [← mul_sub, hz, ← mul_assoc]
  change (C e * C p) * z = 0
  rw [← map_mul, hep, map_zero, zero_mul]

/-- A single generator congruence determines every weighted Laurent value. -/
theorem weighted_hom_of_sub_mem (p e : R) (hep : e * p = 0)
    (f g : L →ₐ[R] L)
    (h : f (T 1) - g (T 1) ∈ (Ideal.span {p}).map (algebraMap R L)) (z : L) :
    C e * f z = C e * g z :=
  weighted_eq_of_sub_mem p e hep _ _
    (LaurentNilpotentReparametrization.hom_sub_mem _ f g h z)

/-- The inverse of the full substitution has the same weighted involutive reduction. -/
theorem weighted_inverse (e : R) (f : L ≃ₐ[R] L) (g : L →ₐ[R] L)
    (hg : Function.Involutive g) (h : ∀ z, C e * f z = C e * g z) (z : L) :
    C e * f.symm z = C e * g z := by
  apply f.injective
  simpa only [map_mul, AlgEquiv.commutes, C_eq_algebraMap, AlgEquiv.apply_symm_apply,
    hg z] using (h (g z)).symm

/-- Two full reciprocal substitutions yield their quotient scaling under the same weight. -/
theorem weighted_normalization (e : R) (f b : L ≃ₐ[R] L) (a w : Rˣ)
    (hf : ∀ z, C e * f z = C e * reciprocal a z)
    (hb : ∀ z, C e * b z = C e * reciprocal w z) (z : L) :
    C e * (b.trans f.symm) z = C e * scaling (w / a) z := by
  have hi := weighted_inverse e f (reciprocal a) (reciprocal_involutive a) hf (b z)
  have hh := congrArg (reciprocal a) (hb z)
  simp only [map_mul, reciprocal_C] at hh
  have hc : (reciprocal a).comp (reciprocal w) = scaling (w / a) := by
    apply LaurentNilpotentReparametrization.hom_ext_positive
    change reciprocal a (reciprocal w (T 1)) = PolygonChartScaling.laurent (w / a) (T 1)
    rw [reciprocal_T, map_mul, reciprocal_C, reciprocal_T_inv,
      PolygonChartScaling.laurent_T_one, ← mul_assoc, ← map_mul]
    rfl
  exact hi.trans (hh.trans (congrArg (fun k : L →ₐ[R] L ↦ C e * k z) hc))

end FLT.Mazur.LaurentWeightedInverse
