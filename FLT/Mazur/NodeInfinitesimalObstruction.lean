/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonQuotient

/-!
# Infinitesimal obstructions at the chart origins

The quadratic terms of the two node equations obstruct lifting tangent vectors
from second to third order, in every characteristic.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace FLT.Mazur.PolygonNodePresentation

open PolygonNodeEqualizer PolygonNodeLocalization
variable {K : Type*} [Field K]

instance eval_ker_isPrime {S : Type*} [CommRing S] [Algebra K S] (e : S →ₐ[K] K) :
    (RingHom.ker e.toRingHom).IsPrime := RingHom.ker_isPrime e.toRingHom

/-- The ideal killing terms of order at least n. -/
def jetIdeal (n : ℕ) : Ideal K[X] := Ideal.span {X ^ n}

/-- Truncated polynomial functions in one infinitesimal parameter. -/
abbrev Jet (K : Type*) [Field K] (n : ℕ) := K[X] ⧸ jetIdeal n

/-- Reduction modulo the nth power of the parameter. -/
def jet (n : ℕ) : K[X] →ₐ[K] Jet K n := Ideal.Quotient.mkₐ K (jetIdeal n)

theorem jet_surjective (n : ℕ) : Function.Surjective (jet (K := K) n) :=
  Ideal.Quotient.mkₐ_surjective K (jetIdeal n)

/-- Equality of jets is equality of their low coefficients. -/
theorem jet_eq_iff (n : ℕ) (p q : K[X]) :
    jet n p = jet n q ↔ ∀ d < n, p.coeff d = q.coeff d := by
  change Ideal.Quotient.mk _ p = Ideal.Quotient.mk _ q ↔ _
  rw [Ideal.Quotient.eq, jetIdeal, Ideal.mem_span_singleton, X_pow_dvd_iff]
  simp only [coeff_sub, sub_eq_zero]

/-- The quotient from third to second order. -/
def jetDrop : Jet K 3 →ₐ[K] Jet K 2 :=
  Ideal.Quotient.liftₐ (jetIdeal 3) (jet 2) (by
    change jetIdeal 3 ≤ RingHom.ker (jet 2).toRingHom
    rw [jetIdeal, Ideal.span_le, Set.singleton_subset_iff]
    change jet 2 (X ^ 3) = 0
    rw [← map_zero (jet 2), jet_eq_iff]
    intro d hd
    simp [coeff_X_pow, show d ≠ 3 by omega])

@[simp] theorem jetDrop_jet (p : K[X]) : jetDrop (jet 3 p) = jet 2 p := rfl

/-- Every second-order jet has a third-order representative. -/
theorem jetDrop_surjective : Function.Surjective (jetDrop (K := K)) := by
  intro z
  obtain ⟨p, rfl⟩ := jet_surjective 2 z
  exact ⟨jet 3 p, rfl⟩

/-- The kernel of the truncation map is square-zero. -/
theorem jetDrop_ker_sq : RingHom.ker (jetDrop (K := K)).toRingHom ^ 2 = ⊥ := by
  apply le_bot_iff.mp
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  obtain ⟨p, rfl⟩ := jet_surjective 3 a
  obtain ⟨q, rfl⟩ := jet_surjective 3 b
  have hp : X ^ 2 ∣ p := by
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)
  have hq : X ^ 2 ∣ q := by
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hb)
  change jet 3 p * jet 3 q = 0
  rw [← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  exact (pow_dvd_pow X (by omega : 3 ≤ 2 + 2)).trans
    (by simpa only [pow_add] using mul_dvd_mul hp hq)

/-- A pair of lifts of the diagonal tangent vector cannot have zero product. -/
theorem jet_mul_obstruction (a b : Jet K 3)
    (ha : jetDrop a = jet 2 X) (hb : jetDrop b = jet 2 X) : a * b ≠ 0 := by
  obtain ⟨p, rfl⟩ := jet_surjective 3 a
  obtain ⟨q, rfl⟩ := jet_surjective 3 b
  have hp := (jet_eq_iff 2 p X).mp ha
  have hq := (jet_eq_iff 2 q X).mp hb
  have hp0 : p.coeff 0 = 0 := by simpa using hp 0 (by omega)
  have hp1 : p.coeff 1 = 1 := by simpa using hp 1 (by omega)
  have hq0 : q.coeff 0 = 0 := by simpa using hq 0 (by omega)
  have hq1 : q.coeff 1 = 1 := by simpa using hq 1 (by omega)
  intro h
  have hc := (jet_eq_iff 3 (p * q) 0).mp (by simpa only [map_mul, map_zero] using h)
  have := hc 2 (by omega)
  simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    hp0, hp1, hq0, hq1] at this

/-- The tangent vector u=0, v=e cannot lift to a point of the cubic. -/
theorem jet_cubic_obstruction (a b : Jet K 3)
    (ha : jetDrop a = 0) (hb : jetDrop b = jet 2 X) : b ^ 2 - a * b - a ^ 3 ≠ 0 := by
  obtain ⟨p, rfl⟩ := jet_surjective 3 a
  obtain ⟨q, rfl⟩ := jet_surjective 3 b
  have hp := (jet_eq_iff 2 p 0).mp (by simpa only [jetDrop_jet, map_zero] using ha)
  have hq := (jet_eq_iff 2 q X).mp hb
  have hp0 : p.coeff 0 = 0 := by simpa using hp 0 (by omega)
  have hp1 : p.coeff 1 = 0 := by simpa using hp 1 (by omega)
  have hq0 : q.coeff 0 = 0 := by simpa using hq 0 (by omega)
  have hq1 : q.coeff 1 = 1 := by simpa using hq 1 (by omega)
  intro h
  have hc := (jet_eq_iff 3 (q ^ 2 - p * q - p ^ 3) 0).mp
    (by simpa only [map_sub, map_pow, map_mul, map_zero] using h)
  have := hc 2 (by omega)
  simp [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, hp0, hp1, hq0, hq1] at this

/-- The diagonal tangent vector of the split node. -/
def aTangent : A (R := K) →ₐ[K] Jet K 2 :=
  aPresent.liftOfSurjective aPresent_surjective (MvPolynomial.aeval ![jet 2 X, jet 2 X])
    (by
      rw [aPresent_ker, aRelation, Ideal.span_le, Set.singleton_subset_iff]
      change MvPolynomial.aeval _ (MvPolynomial.X 0 * MvPolynomial.X 1) = 0
      simp only [map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← map_mul, ← map_zero (jet 2), jet_eq_iff]
      intro d hd
      have hd' : d = 0 ∨ d = 1 := by omega
      rcases hd' with rfl | rfl <;>
        simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.sum_range_succ])

@[simp] theorem aTangent_x : aTangent (x (R := K)) = jet 2 X := by
  rw [← aPresent_X_zero]
  simp only [aTangent, AlgHom.liftOfSurjective_apply, MvPolynomial.aeval_X,
    Matrix.cons_val_zero]

@[simp] theorem aTangent_y : aTangent (y (R := K)) = jet 2 X := by
  rw [← aPresent_X_one]
  simp only [aTangent, AlgHom.liftOfSurjective_apply, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The vertical tangent vector of the one-gon plane cubic. -/
def bTangent : B (R := K) →ₐ[K] Jet K 2 :=
  bPresent.liftOfSurjective bPresent_surjective (MvPolynomial.aeval ![0, jet 2 X]) (by
    rw [bPresent_ker, bRelation, Ideal.span_le, Set.singleton_subset_iff]
    change MvPolynomial.aeval _ bEquation = 0
    simp only [bEquation, map_sub, map_pow, map_mul, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_pow (by omega : 3 ≠ 0),
      sub_zero]
    rw [← map_pow, ← map_zero (jet 2), jet_eq_iff]
    intro d hd
    simp [coeff_X_pow, show d ≠ 2 by omega])

@[simp] theorem bTangent_u : bTangent (u (R := K)) = 0 := by
  rw [← bPresent_X_zero]
  simp only [bTangent, AlgHom.liftOfSurjective_apply, MvPolynomial.aeval_X,
    Matrix.cons_val_zero]

@[simp] theorem bTangent_v : bTangent (v (R := K)) = jet 2 X := by
  rw [← bPresent_X_one]
  simp only [bTangent, AlgHom.liftOfSurjective_apply, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The diagonal tangent map has no lift through the square-zero truncation. -/
theorem aTangent_no_lift (g : A (R := K) →ₐ[K] Jet K 3) :
    jetDrop.comp g ≠ aTangent := by
  intro h
  have hx : jetDrop (g x) = jet 2 X := by simpa using AlgHom.congr_fun h x
  have hy : jetDrop (g y) = jet 2 X := by simpa using AlgHom.congr_fun h y
  exact jet_mul_obstruction _ _ hx hy (by rw [← map_mul, x_mul_y, map_zero])

/-- The vertical tangent map has no lift through the square-zero truncation. -/
theorem bTangent_no_lift (g : B (R := K) →ₐ[K] Jet K 3) :
    jetDrop.comp g ≠ bTangent := by
  intro h
  have hu : jetDrop (g u) = 0 := by simpa using AlgHom.congr_fun h u
  have hv : jetDrop (g v) = jet 2 X := by simpa using AlgHom.congr_fun h v
  exact jet_cubic_obstruction _ _ hu hv (by
    rw [← map_pow, ← map_mul, ← map_sub, ← map_pow, ← map_sub, relation, map_zero])

/-- The constant coefficient of a second-order jet. -/
def jetEval : Jet K 2 →ₐ[K] K :=
  Ideal.Quotient.liftₐ (jetIdeal 2) (aeval 0) (by
    change jetIdeal 2 ≤ RingHom.ker (aeval (0 : K)).toRingHom
    rw [jetIdeal, Ideal.span_le, Set.singleton_subset_iff]
    change aeval (0 : K) (X ^ 2) = 0
    simp)

@[simp] theorem jetEval_jet (p : K[X]) : jetEval (jet 2 p) = p.eval 0 := rfl

/-- Nonzero constant coefficient makes a second-order jet invertible. -/
theorem jet_isUnit (z : Jet K 2) (h : jetEval z ≠ 0) : IsUnit z := by
  obtain ⟨p, rfl⟩ := jet_surjective 2 z
  have hp : p.coeff 0 ≠ 0 := by simpa [← coeff_zero_eq_eval_zero] using h
  refine isUnit_iff_exists_inv.mpr
    ⟨jet 2 (C (p.coeff 0)⁻¹ - C (p.coeff 1 / p.coeff 0 ^ 2) * X), ?_⟩
  change jet 2 p * _ = 1
  rw [← map_mul, ← map_one (jet 2), jet_eq_iff]
  intro d hd
  interval_cases d
  all_goals simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  all_goals field_simp [hp]
  all_goals simp [coeff_one]

/-- A nonliftable tangent map remains obstructed at its origin localization. -/
theorem origin_not_formallySmooth {S : Type*} [CommRing S] [Algebra K S]
    (e : S →ₐ[K] K) (f : S →ₐ[K] Jet K 2) (he : jetEval.comp f = e)
    (hn : ∀ g : S →ₐ[K] Jet K 3, jetDrop.comp g ≠ f) :
    ¬ Algebra.FormallySmooth K (Localization.AtPrime (RingHom.ker e.toRingHom)) := by
  intro h
  let := h
  let L := Localization.AtPrime (RingHom.ker e.toRingHom)
  have hu (y : (RingHom.ker e.toRingHom).primeCompl) : IsUnit (f y) := by
    apply jet_isUnit
    change jetEval.comp f y ≠ 0
    rw [he]
    exact y.property
  let F : L →ₐ[K] Jet K 2 := IsLocalization.liftAlgHom hu
  let G := Algebra.FormallySmooth.liftOfSurjective F jetDrop jetDrop_surjective
    (show IsNilpotent (RingHom.ker jetDrop.toRingHom) from ⟨2, jetDrop_ker_sq⟩)
  apply hn (G.comp (IsScalarTower.toAlgHom K S L))
  ext z
  change jetDrop (G (algebraMap S L z)) = f z
  rw [Algebra.FormallySmooth.liftOfSurjective_apply]
  exact IsLocalization.lift_eq hu z

/-- The local ring of the split node at its origin is not formally smooth. -/
theorem a_origin_not_formallySmooth : ¬ Algebra.FormallySmooth K
    (Localization.AtPrime (RingHom.ker (aEval (R := K)).toRingHom)) := by
  refine origin_not_formallySmooth (K := K) aEval aTangent ?_ aTangent_no_lift
  apply (AlgHom.cancel_right aPresent_surjective).mp
  ext i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, Fin.zero_eta, Fin.mk_one, aPresent_X_zero,
      aPresent_X_one, aTangent_x, aTangent_y, jetEval_jet] <;> simp [aEval]

/-- The local ring of the one-gon chart at its origin is not formally smooth. -/
theorem b_origin_not_formallySmooth : ¬ Algebra.FormallySmooth K
    (Localization.AtPrime (RingHom.ker (bEval (R := K)).toRingHom)) := by
  refine origin_not_formallySmooth (K := K) bEval bTangent ?_ bTangent_no_lift
  apply (AlgHom.cancel_right bPresent_surjective).mp
  ext i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, Fin.zero_eta, Fin.mk_one, bPresent_X_zero,
      bPresent_X_one, bTangent_u, bTangent_v, map_zero, jetEval_jet] <;> simp [bEval, u, v]

end FLT.Mazur.PolygonNodePresentation
