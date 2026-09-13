/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Partial zeta functions of ideal classes

This file defines the Dirichlet-series coefficients obtained by restricting nonzero integral
ideals to one ideal class. The counting identity below is the finite-regrouping core needed for
convergence and for recovering the Dedekind zeta function by summing over the class group.
-/

@[expose] public section

noncomputable section

open Filter Ideal Topology
open scoped ComplexOrder nonZeroDivisors

namespace NumberField

open InfinitePlace NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

/-- The nonzero integral ideals representing a fixed ideal class. -/
def IdealsInClass (C : ClassGroup (𝓞 K)) :=
  {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C}

/-- The number of integral ideals in `C` having absolute norm `n`. -/
def partialZetaCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : IdealsInClass K C // absNorm (I.1.1 : Ideal (𝓞 K)) = n}

/-- The partial zeta function attached to an ideal class. -/
def partialZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (partialZetaCoeff K C n : ℂ)) s

theorem partialZetaCoeff_nonneg (C : ClassGroup (𝓞 K)) (n : ℕ) :
    0 ≤ partialZetaCoeff K C n := by
  exact Nat.zero_le _

private theorem finite_norm_fiber (C : ClassGroup (𝓞 K)) (n : ℕ) :
    Set.Finite {I : IdealsInClass K C | absNorm (I.1.1 : Ideal (𝓞 K)) = n} := by
  let f : IdealsInClass K C → Ideal (𝓞 K) := fun I ↦ I.1.1
  apply Set.Finite.of_finite_image (f := f)
  · apply (Ideal.finite_setOfPred_absNorm_eq n).subset
    rintro J ⟨I, hI, rfl⟩
    exact hI
  · intro I _ J _ hIJ
    apply Subtype.ext
    apply Subtype.ext
    exact hIJ

private theorem finite_nonzero_norm (n : ℕ) :
    Set.Finite {I : (Ideal (𝓞 K))⁰ | absNorm (I : Ideal (𝓞 K)) = n} := by
  let f : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K) := fun I ↦ I.1
  apply Set.Finite.of_finite_image (f := f)
  · apply (Ideal.finite_setOfPred_absNorm_eq n).subset
    rintro J ⟨I, hI, rfl⟩
    exact hI
  · exact fun I _ J _ hIJ ↦ Subtype.ext hIJ

private def classFiberEquiv (C : ClassGroup (𝓞 K)) (n : ℕ) :
    {I : {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} //
        ClassGroup.mk0 I.1 = C} ≃
      {I : IdealsInClass K C // absNorm (I.1.1 : Ideal (𝓞 K)) = n} where
  toFun I := ⟨⟨I.1.1, I.2⟩, I.1.2⟩
  invFun I := ⟨⟨I.1.1, I.2⟩, I.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def idealNormEquivNonzeroNorm {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) // absNorm I = n} ≃
      {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} where
  toFun I := ⟨⟨I.1, by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hI
    apply hn
    rw [← I.2, Ideal.absNorm_eq_zero_iff]
    exact hI⟩, I.2⟩
  invFun I := ⟨I.1.1, I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Summing exact-norm coefficients gives the number of representatives in the indicated range. -/
theorem sum_partialZetaCoeff_Icc (C : ClassGroup (𝓞 K)) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, partialZetaCoeff K C k =
      Nat.card {I : IdealsInClass K C //
        absNorm (I.1.1 : Ideal (𝓞 K)) ∈ Finset.Icc 1 n} := by
  change (∑ k ∈ Finset.Icc 1 n,
      Nat.card {I : IdealsInClass K C // absNorm (I.1.1 : Ideal (𝓞 K)) = k}) = _
  exact (Finset.card_preimage_eq_sum_card_image_eq
    (f := fun I : IdealsInClass K C ↦ absNorm (I.1.1 : Ideal (𝓞 K)))
    (s := Finset.Icc 1 n) (fun k _ ↦ finite_norm_fiber K C k)).symm

/-- At positive norm, the classwise coefficients partition all integral ideals. -/
theorem sum_partialZetaCoeff (n : ℕ) (hn : n ≠ 0) :
    ∑ C : ClassGroup (𝓞 K), partialZetaCoeff K C n =
      Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  classical
  let S := {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n}
  let _ : Fintype S := (finite_nonzero_norm K n).fintype
  let _ : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  calc
    ∑ C : ClassGroup (𝓞 K), partialZetaCoeff K C n =
        ∑ C : ClassGroup (𝓞 K), Nat.card {I : S // ClassGroup.mk0 I.1 = C} := by
          apply Finset.sum_congr rfl
          intro C _
          exact (Nat.card_congr (classFiberEquiv K C n)).symm
    _ = Fintype.card S := by
      rw [Fintype.card, Finset.card_eq_sum_card_fiberwise
        (f := fun I : S ↦ ClassGroup.mk0 I.1) (s := Finset.univ) (t := Finset.univ)
        (fun _ _ ↦ Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro C _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr (idealNormEquivNonzeroNorm K hn).symm

/-- A classwise coefficient is bounded by the corresponding Dedekind-zeta coefficient. -/
theorem partialZetaCoeff_le_dedekindZetaCoeff (C : ClassGroup (𝓞 K))
    (n : ℕ) (hn : n ≠ 0) :
    partialZetaCoeff K C n ≤ Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  rw [← sum_partialZetaCoeff K n hn]
  exact Finset.single_le_sum (f := fun D : ClassGroup (𝓞 K) ↦ partialZetaCoeff K D n)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ C)

private def idealsInClassNormRangeEquiv (C : ClassGroup (𝓞 K)) (n : ℕ) :
    {I : IdealsInClass K C //
        absNorm (I.1.1 : Ideal (𝓞 K)) ∈ Finset.Icc 1 n} ≃
      {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ n ∧ ClassGroup.mk0 I = C} where
  toFun I := ⟨I.1.1, (Finset.mem_Icc.mp I.2).2, I.1.2⟩
  invFun I := ⟨⟨I.1, I.2.2⟩, (Finset.mem_Icc.mpr
    ⟨absNorm_pos_of_nonZeroDivisors I.1, I.2.1⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem tendsto_partialZetaCoeff_sum_div (C : ClassGroup (𝓞 K)) :
    Tendsto (fun n : ℕ ↦
      ((∑ k ∈ Finset.Icc 1 n, partialZetaCoeff K C k : ℕ) : ℝ) / n) atTop
      (nhds (((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K) /
        (torsionOrder K * Real.sqrt |discr K|)))) := by
  have h := (Ideal.tendsto_norm_le_and_mk_eq_div_atTop K C).comp
    tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun n ↦ ?_)
  dsimp only [Function.comp_apply]
  congr 1
  rw [sum_partialZetaCoeff_Icc]
  exact_mod_cast (Nat.card_congr (idealsInClassNormRangeEquiv K C n)).symm

/-- The coefficients of a partial zeta function are absolutely summable on `re s > 1`. -/
theorem partialZeta_summable (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (partialZetaCoeff K C n : ℂ)) s := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1)
  · exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
      (by simpa [Nat.cast_sum, Real.rpow_one] using tendsto_partialZetaCoeff_sum_div K C)
  · exact fun n ↦ Nat.cast_nonneg (partialZetaCoeff K C n)
  · exact zero_le_one
  · exact hs

/-- A partial zeta function is analytic on the half-plane `re s > 1`. -/
theorem partialZeta_analyticOn (C : ClassGroup (𝓞 K)) :
    AnalyticOn ℂ (partialZeta K C) {s : ℂ | 1 < s.re} := by
  let f : ℕ → ℂ := fun n ↦ partialZetaCoeff K C n
  have habs : LSeries.abscissaOfAbsConv f ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
      partialZeta_summable K C hy
  exact (LSeries_analyticOn f).mono fun s hs ↦ habs.trans_lt (by exact_mod_cast hs)

/-- The finite sum of the partial zeta functions is the Dedekind zeta function on `re s > 1`. -/
theorem sum_partialZeta_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K), partialZeta K C s = dedekindZeta K s := by
  let f : ClassGroup (𝓞 K) → ℕ → ℂ := fun C n ↦ partialZetaCoeff K C n
  calc
    ∑ C : ClassGroup (𝓞 K), partialZeta K C s =
        ∑ C ∈ Finset.univ, LSeries (f C) s := by simp [partialZeta, f]
    _ = LSeries (∑ C ∈ Finset.univ, f C) s := by
      symm
      apply LSeries_sum
      intro C _
      exact partialZeta_summable K C hs
    _ = dedekindZeta K s := by
      rw [dedekindZeta]
      apply LSeries_congr
      intro n hn
      simp only [Finset.sum_apply, f]
      exact_mod_cast sum_partialZetaCoeff K n hn

/-- On the real half-line of convergence, each partial zeta is nonnegative. -/
theorem partialZeta_nonneg (C : ClassGroup (𝓞 K)) (x : ℝ) :
    0 ≤ partialZeta K C x := by
  rw [partialZeta, LSeries]
  exact tsum_nonneg fun n ↦ LSeries.term_nonneg (by exact_mod_cast Nat.zero_le _) x

/-- The crude real-axis bound by the full Dedekind zeta function. -/
theorem partialZeta_le_dedekindZeta (C : ClassGroup (𝓞 K)) {x : ℝ} (hx : 1 < x) :
    partialZeta K C x ≤ dedekindZeta K x := by
  rw [← sum_partialZeta_eq_dedekindZeta K (by simpa using hx)]
  exact Finset.single_le_sum (fun D _ ↦ partialZeta_nonneg K D x) (Finset.mem_univ C)

private theorem norm_partialZetaTerm_eq_re_realTerm (a : ℕ → ℕ) (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun k ↦ (a k : ℂ)) s n‖ =
      (LSeries.term (fun k ↦ (a k : ℂ)) (s.re : ℂ) n).re := by
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ite_eq_right hn, LSeries.term_of_ne_zero hn]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast]
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_div]
    simp

/-- The crude complex bound: a partial zeta is dominated by the real Dedekind zeta at `re s`. -/
theorem norm_partialZeta_le_dedekindZeta_re (C : ClassGroup (𝓞 K))
    {s : ℂ} (hs : 1 < s.re) :
    ‖partialZeta K C s‖ ≤ (dedekindZeta K (s.re : ℂ)).re := by
  let f : ℕ → ℂ := fun n ↦ partialZetaCoeff K C n
  have hsum : Summable (LSeries.term f s) := partialZeta_summable K C hs
  have hsum_re : Summable (LSeries.term f (s.re : ℂ)) :=
    partialZeta_summable K C (by simpa using hs)
  calc
    ‖partialZeta K C s‖ = ‖∑' n, LSeries.term f s n‖ := by rfl
    _ ≤ ∑' n, ‖LSeries.term f s n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_iff.mpr hsum)
    _ = ∑' n, (LSeries.term f (s.re : ℂ) n).re := by
      apply tsum_congr
      exact norm_partialZetaTerm_eq_re_realTerm (partialZetaCoeff K C) s
    _ = (partialZeta K C (s.re : ℂ)).re := by
      rw [partialZeta, LSeries, Complex.re_tsum hsum_re]
    _ ≤ (dedekindZeta K (s.re : ℂ)).re :=
      Complex.re_le_re (partialZeta_le_dedekindZeta K C hs)

end NumberField
