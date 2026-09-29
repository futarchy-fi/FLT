/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologyCoordinates
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Contraction of exponent summands

Inserting an index with nonnegative exponent preserves the support condition.
This gives an explicit contraction in positive degrees of the actual monomial
summand. No finiteness or reducedness assumption on the base ring is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

open TwistGradedCech

variable (R : Type u) [CommRing R] (ι : Type u)
variable (n : ℤ) (e : ι →₀ ℤ) (i : ι) (hi : 0 ≤ e i)

include hi

/-- Inserting a nonnegative index does not change which exponents are supported. -/
lemma supported_cons_iff {m : ℕ} (a : Fin m → ι) :
    Supported ι n e (Fin.cons i a) ↔ Supported ι n e a := by
  constructor
  · intro h
    refine ⟨h.1, fun j hj ↦ ?_⟩
    by_cases hji : j = i
    · simpa only [hji] using hi
    · exact h.2 j (by simpa only [Fin.range_cons, Set.mem_insert_iff, not_or] using ⟨hji, hj⟩)
  · intro h
    refine ⟨h.1, fun j hj ↦ h.2 j ?_⟩
    exact fun hj' ↦ hj (by rw [Fin.range_cons]; exact Set.mem_insert_of_mem i hj')

/-- Insertion of a nonnegative index lowers supported scalar cochain degree. -/
def scalarHomotopy (q : ℕ) :
    scalarTerm R ι n e (q + 1) →ₗ[R] scalarTerm R ι n e q where
  toFun x := ⟨fun a ↦ x.val (Fin.cons i a), fun a ha ↦
    x.property _ (fun h ↦ ha ((supported_cons_iff ι n e i hi a).mp h))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The insertion contraction identity in every positive degree. -/
lemma scalarHomotopy_identity (q : ℕ) (x : scalarTerm R ι n e (q + 1)) :
    scalarHomotopy R ι n e i hi (q + 1) (scalarDifferential R ι n e (q + 1) x) +
      scalarDifferential R ι n e q (scalarHomotopy R ι n e i hi q x) = x := by
  apply Subtype.ext
  funext a
  change (∑ k : Fin (q + 3), (-1 : ℤ) ^ (k : ℕ) •
      x.val (Fin.cons i a ∘ k.succAbove)) +
    (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
      x.val (Fin.cons i (a ∘ k.succAbove))) = x.val a
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.succAbove_zero,
    Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, Finset.sum_neg_distrib]
  change x.val a + -(∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
    x.val (Fin.cons i (a ∘ k.succAbove))) +
    (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
      x.val (Fin.cons i (a ∘ k.succAbove))) = x.val a
  abel

/-- Transport insertion back to the actual B10 exponent subcomplex. -/
def exponentHomotopy (q : ℕ) :
    exponentSummand R ι n (q + 1) e →ₗ[R] exponentSummand R ι n q e :=
  (scalarEquiv R ι n e q).symm.toLinearMap.comp
    ((scalarHomotopy R ι n e i hi q).comp (scalarEquiv R ι n e (q + 1)).toLinearMap)

lemma scalarEquiv_homotopy (q : ℕ) (x : exponentSummand R ι n (q + 1) e) :
    scalarEquiv R ι n e q (exponentHomotopy R ι n e i hi q x) =
      scalarHomotopy R ι n e i hi q (scalarEquiv R ι n e (q + 1) x) :=
  (scalarEquiv R ι n e q).apply_symm_apply _

/-- The original exponent differential satisfies the explicit contraction identity. -/
lemma exponentHomotopy_identity (q : ℕ) (x : exponentSummand R ι n (q + 1) e) :
    exponentHomotopy R ι n e i hi (q + 1) (exponentDifferential R ι n (q + 1) e x) +
      exponentDifferential R ι n q e (exponentHomotopy R ι n e i hi q x) = x := by
  apply (scalarEquiv R ι n e (q + 1)).injective
  rw [map_add, scalarEquiv_homotopy, scalarEquiv_d, scalarEquiv_d, scalarEquiv_homotopy]
  exact scalarHomotopy_identity R ι n e i hi q _

/-- Every positive-degree cocycle in this actual exponent summand is a coboundary. -/
lemma exponent_cocycle_boundary (q : ℕ) (x : exponentSummand R ι n (q + 1) e)
    (hx : exponentDifferential R ι n (q + 1) e x = 0) :
    exponentDifferential R ι n q e (exponentHomotopy R ι n e i hi q x) = x := by
  have h := exponentHomotopy_identity R ι n e i hi q x
  simpa only [hx, map_zero, zero_add] using h

/-- An exponent with a nonnegative coordinate has no positive Cech cohomology. -/
lemma exponent_exactAt_succ (q : ℕ) : (exponentComplex R ι n e).ExactAt (q + 1) := by
  rw [(exponentComplex R ι n e).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  simp [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    exponentComplex, CochainComplex.of.d] at hx
  refine ⟨exponentHomotopy R ι n e i hi q x, ?_⟩
  simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    exponentComplex, CochainComplex.of.d] using exponent_cocycle_boundary R ι n e i hi q x hx

/-- Vanishing is stated for the cohomology object of the actual B10 subcomplex. -/
lemma exponent_isZero_homology_succ (q : ℕ) :
    Limits.IsZero ((exponentComplex R ι n e).homology (q + 1)) :=
  (exponent_exactAt_succ R ι n e i hi q).isZero_homology

omit hi in
/-- Every scalar zero-cocycle is constant on singleton tuples. -/
lemma scalar_zero_cocycle_constant (x : scalarTerm R ι n e 0)
    (hx : scalarDifferential R ι n e 0 x = 0) (a : Fin 1 → ι) :
    x.val a = x.val (fun _ ↦ i) := by
  have h := congrArg (fun z : scalarTerm R ι n e 1 ↦ z.val (Fin.cons i a)) hx
  change (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
    x.val (Fin.cons i a ∘ k.succAbove)) = 0 at h
  have he : Fin.cons i a ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 ↦ i := by
    ext j
    fin_cases j
    rfl
  rw [Fin.sum_univ_two] at h
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.succAbove_zero,
    Fin.cons_comp_succ, Fin.val_one, pow_one, neg_one_zsmul, he] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

/-- A mixed-sign exponent has no zero-cocycles either. -/
lemma scalar_zero_cocycle_eq_zero (j : ι) (hj : e j < 0)
    (x : scalarTerm R ι n e 0) (hx : scalarDifferential R ι n e 0 x = 0) : x = 0 := by
  have hji : j ≠ i := by
    intro h
    subst j
    omega
  have hs : ¬ Supported ι n e (fun _ : Fin 1 ↦ i) := by
    intro h
    have hnonneg := h.2 j (by simpa only [Set.mem_range, not_exists] using
      (fun _ : Fin 1 ↦ Ne.symm hji))
    omega
  apply Subtype.ext
  funext a
  exact (scalar_zero_cocycle_constant R ι n e i x hx a).trans (x.property _ hs)

/-- Exactness at zero for an exponent with both a negative and a nonnegative entry. -/
lemma exponent_exactAt_zero (j : ι) (hj : e j < 0) :
    (exponentComplex R ι n e).ExactAt 0 := by
  rw [(exponentComplex R ι n e).exactAt_iff' 0 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hd : exponentDifferential R ι n 0 e x = 0 := by
    simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
      exponentComplex, CochainComplex.of.d] using hx
  have hs : scalarDifferential R ι n e 0 (scalarEquiv R ι n e 0 x) = 0 := by
    rw [← scalarEquiv_d, hd, map_zero]
  have hz : x = 0 := (scalarEquiv R ι n e 0).injective (by
    rw [map_zero]
    exact scalar_zero_cocycle_eq_zero R ι n e i hi j hj _ hs)
  exact ⟨0, by simp [hz]⟩

/-- Every cohomology object of a mixed-sign exponent subcomplex vanishes. -/
lemma exponent_isZero_homology_mixed (j : ι) (hj : e j < 0) (q : ℕ) :
    Limits.IsZero ((exponentComplex R ι n e).homology q) := by
  cases q with
  | zero => exact (exponent_exactAt_zero R ι n e i hi j hj).isZero_homology
  | succ q => exact exponent_isZero_homology_succ R ι n e i hi q

omit hi in
/-- An all-negative exponent requires the tuple to contain every chart index. -/
lemma supported_surjective_of_negative {m : ℕ} (a : Fin m → ι)
    (hneg : ∀ j, e j < 0) (ha : Supported ι n e a) : Function.Surjective a := by
  intro j
  by_contra hj
  exact (not_le_of_gt (hneg j)) (ha.2 j hj)

omit hi in
/-- Below the top degree, an all-negative exponent has zero cochain term. -/
lemma exponent_eq_zero_of_negative [Fintype ι] (q : ℕ)
    (hq : q + 1 < Fintype.card ι) (hneg : ∀ j, e j < 0)
    (x : exponentSummand R ι n q e) : x = 0 := by
  apply (scalarEquiv R ι n e q).injective
  rw [map_zero]
  apply Subtype.ext
  funext a
  apply (scalarEquiv R ι n e q x).property a
  intro ha
  have hc := Fintype.card_le_of_surjective a (supported_surjective_of_negative ι n e a hneg ha)
  simp only [Fintype.card_fin] at hc
  omega

omit hi in
/-- All-negative exponent cohomology vanishes strictly below the top degree. -/
lemma exponent_isZero_homology_of_negative [Fintype ι] (q : ℕ)
    (hq : q + 1 < Fintype.card ι) (hneg : ∀ j, e j < 0) :
    Limits.IsZero ((exponentComplex R ι n e).homology q) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ ?_⟩
  exact (exponent_eq_zero_of_negative R ι n e q hq hneg x).trans
    (exponent_eq_zero_of_negative R ι n e q hq hneg y).symm

omit hi in
/-- Every exponent summand vanishes in the intermediate positive degrees. -/
lemma exponent_isZero_homology_intermediate [Fintype ι] (q : ℕ)
    (hq : q + 2 < Fintype.card ι) :
    Limits.IsZero ((exponentComplex R ι n e).homology (q + 1)) := by
  by_cases h : ∃ j, 0 ≤ e j
  · obtain ⟨j, hj⟩ := h
    exact exponent_isZero_homology_succ R ι n e j hj q
  · push Not at h
    exact exponent_isZero_homology_of_negative R ι n e (q + 1) hq h

omit hi in
/-- The degree of an all-negative exponent is at most minus the number of variables. -/
lemma degree_le_neg_card [Fintype ι] (hneg : ∀ j, e j < 0) :
    e.degree ≤ -(Fintype.card ι : ℤ) := by
  rw [Finsupp.degree_eq_sum]
  calc
    ∑ j, e j ≤ ∑ _j : ι, (-1 : ℤ) := Finset.sum_le_sum (fun j _ ↦ by
      have := hneg j
      omega)
    _ = -(Fintype.card ι : ℤ) := by simp

omit hi in
/-- Above the top-degree threshold, every degree-n exponent has no positive cohomology. -/
lemma exponent_isZero_homology_large [Fintype ι] (he : e.degree = n)
    (hn : -(Fintype.card ι : ℤ) < n) (q : ℕ) :
    Limits.IsZero ((exponentComplex R ι n e).homology (q + 1)) := by
  have h : ∃ j, 0 ≤ e j := by
    by_contra h
    push Not at h
    have hd := degree_le_neg_card ι e h
    omega
  obtain ⟨j, hj⟩ := h
  exact exponent_isZero_homology_succ R ι n e j hj q

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
