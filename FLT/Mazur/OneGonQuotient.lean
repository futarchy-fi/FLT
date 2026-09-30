/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeQuotient
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The equation of the one-gon chart

Reduction by the monic equation in `v` leaves `a(u) + b(u)v`. Its two terms
have different degree parity on the normalization, so the remainder is unique.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.PolygonNodePresentation

variable {R : Type*} [CommRing R]

/-- The two generators of the pinched affine line. -/
def bPresent : MvPolynomial (Fin 2) R →ₐ[R] B (R := R) :=
  MvPolynomial.aeval ![u, v]

@[simp] theorem bPresent_X_zero : bPresent (MvPolynomial.X 0) = u (R := R) := by
  simp [bPresent]

@[simp] theorem bPresent_X_one : bPresent (MvPolynomial.X 1) = v (R := R) := by
  simp [bPresent]

/-- The generator map covers the actual pinching subalgebra. -/
theorem bPresent_surjective : Function.Surjective (bPresent (R := R)) := by
  have he : (B (R := R)).val.comp bPresent =
      MvPolynomial.aeval ![(u (R := R)).val, (v (R := R)).val] := by
    ext i
    fin_cases i <;> simp [bPresent]
  have hr : ((B (R := R)).val.comp bPresent).range = B := by
    rw [he, ← Algebra.adjoin_range_eq_range_aeval]
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] using (b_adjoin (R := R))
  intro p
  obtain ⟨q, hq⟩ := show p.val ∈ ((B (R := R)).val.comp bPresent).range from
    by rw [hr]; exact p.property
  exact ⟨q, Subtype.ext hq⟩

/-- The plane cubic defining the one-gon chart. -/
def bEquation : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3

/-- The principal ideal of the plane cubic. -/
def bRelation : Ideal (MvPolynomial (Fin 2) R) := Ideal.span {bEquation}

theorem bRelation_le_ker : bRelation ≤ RingHom.ker (bPresent (R := R)).toRingHom := by
  rw [bRelation, Ideal.span_le, Set.singleton_subset_iff]
  change bPresent bEquation = 0
  simpa [bEquation] using (relation (R := R))

/-- Reduction of every polynomial to degree at most one in the second coordinate. -/
theorem b_normalForm (p : MvPolynomial (Fin 2) R) :
    let q := Ideal.Quotient.mkₐ R (bRelation (R := R))
    ∃ a b : R[X], q p = aeval (q (MvPolynomial.X 0)) a +
      aeval (q (MvPolynomial.X 0)) b * q (MvPolynomial.X 1) := by
  let q := Ideal.Quotient.mkₐ R (bRelation (R := R))
  have hr : q (MvPolynomial.X 1) ^ 2 =
      q (MvPolynomial.X 0) * q (MvPolynomial.X 1) + q (MvPolynomial.X 0) ^ 3 := by
    have h : q (bEquation (R := R)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp only [bEquation, map_sub, map_mul, map_pow] at h
    linear_combination h
  change ∃ a b, q p = _
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨C r, 0, by simp [q]⟩
  | add p s hp hs =>
    obtain ⟨a, b, ha⟩ := hp
    obtain ⟨c, d, hc⟩ := hs
    exact ⟨a + c, b + d, by simp only [map_add, ha, hc]; ring⟩
  | mul_X p i hp =>
    obtain ⟨a, b, ha⟩ := hp
    fin_cases i
    · refine ⟨a * X, b * X, ?_⟩
      simp only [map_mul, ha, aeval_X]
      simp only [q, Fin.zero_eta] at *
      ring
    · refine ⟨b * X ^ 3, a + b * X, ?_⟩
      simp only [map_mul, map_add, map_pow, aeval_X, ha]
      simp only [q, Fin.mk_one] at *
      linear_combination aeval (q (MvPolynomial.X 0)) b * hr

variable {K : Type*} [Field K]

/-- Degree parity separates the two terms in the normal form on the normalization. -/
theorem b_normalForm_unique (a b : K[X])
    (h : a.comp (u (R := K)).val + b.comp (u (R := K)).val * (v (R := K)).val = 0) :
    a = 0 ∧ b = 0 := by
  have hu : (u (R := K)).val.natDegree = 2 := by
    change (X * (X - 1) : K[X]).natDegree = 2
    compute_degree!
  have hv : (v (R := K)).val.natDegree = 3 := by
    change (X * (X * (X - 1)) : K[X]).natDegree = 3
    compute_degree!
  have hu0 : (u (R := K)).val ≠ 0 := by
    intro h0
    simp [h0] at hu
  have hv0 : (v (R := K)).val ≠ 0 := by
    intro h0
    simp [h0] at hv
  have hb : b = 0 := by
    by_contra hb
    have hb' : b.comp (u (R := K)).val ≠ 0 := by
      exact fun h0 ↦ by
        rcases comp_eq_zero_iff.mp h0 with ha | ⟨_, hc⟩
        · exact hb ha
        · have := congrArg natDegree hc; simp [hu] at this
    have hd := congrArg natDegree (eq_neg_of_add_eq_zero_left h)
    rw [natDegree_neg, natDegree_comp, natDegree_mul hb' hv0, natDegree_comp, hu, hv] at hd
    omega
  refine ⟨?_, hb⟩
  simp only [hb, zero_comp, zero_mul, add_zero] at h
  rcases comp_eq_zero_iff.mp h with ha | ⟨_, hc⟩
  · exact ha
  · have := congrArg natDegree hc; simp [hu] at this

/-- The cubic equation generates the entire presentation kernel. -/
theorem bPresent_ker : RingHom.ker (bPresent (R := K)).toRingHom = bRelation := by
  apply le_antisymm
  · intro p hp
    obtain ⟨a, b, h⟩ := b_normalForm p
    let f := Ideal.Quotient.liftₐ (bRelation (R := K)) bPresent bRelation_le_ker
    have hfq (s) : f (Ideal.Quotient.mkₐ K bRelation s) = bPresent s := rfl
    have hf := congrArg f h
    have hp' : bPresent p = 0 := hp
    simp only [map_add, map_mul, ← aeval_algHom_apply, hfq,
      bPresent_X_zero, bPresent_X_one, hp'] at hf
    have hab : a = 0 ∧ b = 0 := by
      apply b_normalForm_unique
      have hf' := congrArg (B (R := K)).val hf
      simpa only [map_zero, map_add, map_mul, ← aeval_algHom_apply,
        ← comp_eq_aeval, Subalgebra.val_apply] using hf'.symm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [hab.1, hab.2, map_zero, zero_mul, add_zero,
      Ideal.Quotient.mkₐ_eq_mk] using h
  · exact bRelation_le_ker

/-- The plane cubic is isomorphic to the actual one-gon chart algebra. -/
def bQuotientEquiv : (MvPolynomial (Fin 2) K ⧸ bRelation) ≃ₐ[K] B (R := K) :=
  (Ideal.quotientEquivAlgOfEq K bPresent_ker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective bPresent_surjective)

end FLT.Mazur.PolygonNodePresentation
