/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.AINTLIB.DedekindResidue.ExplicitFormula.GRHZeros
public import FLT.Odlyzko.ZeroSideOffCritical

/-!
# Symmetry of the Dedekind zeta zero divisor

The functional equation and conjugation symmetry preserve the multiplicities in the
zero divisor of the completed Dedekind zeta.  This lifts the functional-equation
involution to the indexed zero type and proves nonnegativity of every bounded zero
window under the Poitou boundary hypotheses.
-/

@[expose] public section

open Complex Filter
open scoped ComplexConjugate FourierTransform

namespace DedekindResidue

variable (K : Type*) [Field K] [NumberField K]

private theorem dedekindZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K (conj s) = conj (NumberField.dedekindZeta K s) := by
  rw [Chebotarev.dedekindZeta_eq_tsum_idealNormMultiplicity K (by simpa),
    Chebotarev.dedekindZeta_eq_tsum_idealNormMultiplicity K hs, conj_tsum]
  refine tsum_congr fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [Chebotarev.idealNormMultiplicity_zero]
  · rw [map_mul, map_natCast, show -(conj s) = conj (-s) by simp,
      Complex.cpow_conj]
    · simp
    · rw [Complex.natCast_arg]
      positivity

private theorem completedZetaPrefactor_conj (s : ℂ) :
    completedZetaPrefactor K (conj s) = conj (completedZetaPrefactor K s) := by
  have hcpow (x : ℝ) (hx : 0 ≤ x) (w : ℂ) :
      (x : ℂ) ^ conj w = conj ((x : ℂ) ^ w) := by
    simpa using Complex.cpow_conj (x : ℂ) w (by
      rw [Complex.arg_ofReal_of_nonneg hx]
      positivity)
  have hGammaR : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
    rw [show -(conj s) / 2 = conj (-s / 2) by
        rw [map_div₀, map_neg, map_ofNat],
      hcpow Real.pi Real.pi_pos.le,
      show conj s / 2 = conj (s / 2) by rw [map_div₀, map_ofNat],
      Complex.Gamma_conj]
  have hGammaC : Complex.Gammaℂ (conj s) = conj (Complex.Gammaℂ s) := by
    rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def, map_mul, map_mul]
    rw [map_ofNat]
    rw [show (2 : ℂ) * Real.pi = (((2 : ℝ) * Real.pi : ℝ) : ℂ) by norm_num,
      show -(conj s) = conj (-s) by simp,
      hcpow (2 * Real.pi) (by positivity), Complex.Gamma_conj]
  unfold completedZetaPrefactor gammaFactor
  rw [map_mul, map_mul, map_pow, map_pow, hGammaR, hGammaC]
  rw [show conj s / 2 = conj (s / 2) by rw [map_div₀, map_ofNat],
    hcpow (|NumberField.discr K| : ℝ) (abs_nonneg _)]

@[simp] theorem completedDedekindZetaEntire_conj (s : ℂ) :
    completedDedekindZetaEntire K (conj s) =
      conj (completedDedekindZetaEntire K s) := by
  let H := completedDedekindZetaEntire K
  have hstarDiff : Differentiable ℂ (fun z ↦ conj (H (conj z))) := fun z ↦ by
    have hd := ((differentiable_completedDedekindZetaEntire K) (conj z)).conj_conj
    simpa [H, Function.comp_def] using hd
  have hstar : AnalyticOnNhd ℂ (fun z ↦ conj (H (conj z))) Set.univ :=
    fun z _ ↦ hstarDiff.analyticAt z
  have hH : AnalyticOnNhd ℂ H Set.univ := fun z _ ↦
    (differentiable_completedDedekindZetaEntire K).analyticAt z
  have hagree (z : ℂ) (hz : 1 < z.re) : conj (H (conj z)) = H z := by
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    have hzc0 : conj z ≠ 0 := by
      intro h
      apply hz0
      simpa using congrArg conj h
    have hzc1 : conj z ≠ 1 := by
      intro h
      apply hz1
      simpa using congrArg conj h
    dsimp [H]
    rw [completedDedekindZetaEntire_eq K hzc0 hzc1,
      completedDedekindZetaEntire_eq K hz0 hz1,
      completedDedekindZeta_eq_of_one_lt_re K (by simpa),
      completedDedekindZeta_eq_of_one_lt_re K hz,
      completedZetaPrefactor_conj K,
      dedekindZeta_conj_of_one_lt_re K hz]
    simp
  have heq : (fun z ↦ conj (H (conj z))) = H :=
    hstar.eq_of_eventuallyEq hH
      (eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by norm_num : (1 : ℝ) < (2 : ℂ).re))
        hagree)
  simpa [H] using congrArg conj (congrFun heq s)

private theorem analyticOrderAt_completedDedekindZetaEntire_conj (z : ℂ) :
    analyticOrderAt (completedDedekindZetaEntire K) (conj z) =
      analyticOrderAt (completedDedekindZetaEntire K) z := by
  let H := completedDedekindZetaEntire K
  let Hstar : ℂ → ℂ := fun w ↦ conj (H (conj w))
  have hH (w : ℂ) : AnalyticAt ℂ H w :=
    (differentiable_completedDedekindZetaEntire K).analyticAt w
  have hHstar (w : ℂ) : AnalyticAt ℂ Hstar w := by
    have hdiff : Differentiable ℂ Hstar := fun u ↦ by
      have hd := ((differentiable_completedDedekindZetaEntire K) (conj u)).conj_conj
      simpa [Hstar, H, Function.comp_def] using hd
    exact hdiff.analyticAt w
  have hiter : ∀ n : ℕ, iteratedDeriv n Hstar = conj ∘ iteratedDeriv n H ∘ conj := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]
  have horder : analyticOrderAt Hstar (conj z) = analyticOrderAt H z := by
    refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hHstar (conj z)),
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH z)]
    constructor <;> intro h i hi
    · have hi0 := h i hi
      rw [hiter i] at hi0
      simpa using hi0
    · rw [hiter i]
      simpa using h i hi
  calc
    analyticOrderAt H (conj z) = analyticOrderAt Hstar (conj z) := by
      apply analyticOrderAt_congr
      exact Filter.Eventually.of_forall fun w ↦ by simp [Hstar, H]
    _ = analyticOrderAt H z := horder

/-- Complex conjugation preserves multiplicity in the completed zeta zero divisor. -/
theorem zetaZeroDivisor_conj (z : ℂ) :
    zetaZeroDivisor K (conj z) = zetaZeroDivisor K z := by
  have hH (w : ℂ) : AnalyticAt ℂ (completedDedekindZetaEntire K) w :=
    (differentiable_completedDedekindZetaEntire K).analyticAt w
  rw [zetaZeroDivisor,
    MeromorphicOn.divisor_apply (fun w _ ↦ (hH w).meromorphicAt) (Set.mem_univ (conj z)),
    MeromorphicOn.divisor_apply (fun w _ ↦ (hH w).meromorphicAt) (Set.mem_univ z),
    (hH (conj z)).meromorphicOrderAt_eq, (hH z).meromorphicOrderAt_eq]
  rw [analyticOrderAt_completedDedekindZetaEntire_conj K]

/-- The functional equation preserves multiplicity in the completed zeta zero divisor. -/
theorem zetaZeroDivisor_one_sub (z : ℂ) :
    zetaZeroDivisor K (1 - z) = zetaZeroDivisor K z := by
  have hH (w : ℂ) : AnalyticAt ℂ (completedDedekindZetaEntire K) w :=
    (differentiable_completedDedekindZetaEntire K).analyticAt w
  rw [zetaZeroDivisor,
    MeromorphicOn.divisor_apply (fun w _ ↦ (hH w).meromorphicAt)
      (Set.mem_univ (1 - z)),
    MeromorphicOn.divisor_apply (fun w _ ↦ (hH w).meromorphicAt) (Set.mem_univ z),
    (hH (1 - z)).meromorphicOrderAt_eq, (hH z).meromorphicOrderAt_eq]
  congr 1
  let r : ℂ → ℂ := fun w ↦ 1 - w
  have hr : AnalyticAt ℂ r z := by fun_prop
  have hr' : deriv r z ≠ 0 := by
    have hderiv : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z := by
      exact (hasDerivAt_id z).const_sub 1
    change deriv (fun w : ℂ ↦ 1 - w) z ≠ 0
    rw [hderiv.deriv]
    norm_num
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := completedDedekindZetaEntire K) hr hr'
  have hfun : completedDedekindZetaEntire K ∘ r = completedDedekindZetaEntire K := by
    funext w
    exact completedDedekindZetaEntire_one_sub K w
  rw [hfun] at hcomp
  dsimp [r] at hcomp
  exact congrArg (ENat.map Nat.cast) hcomp.symm

/-- The Poitou functional-equation partner preserves completed-zeta multiplicity. -/
theorem zetaZeroDivisor_functionalEquationPartner (z : ℂ) :
    zetaZeroDivisor K (Odlyzko.functionalEquationPartner z) = zetaZeroDivisor K z := by
  rw [Odlyzko.functionalEquationPartner, zetaZeroDivisor_one_sub,
    zetaZeroDivisor_conj]

end DedekindResidue

namespace Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- The functional-equation involution on the indexed zeros of the completed Dedekind zeta. -/
def zetaZeroPartner : DedekindResidue.ZetaZeros K ≃ DedekindResidue.ZetaZeros K where
  toFun ρ := ⟨functionalEquationPartner ρ.1, by
    rw [DedekindResidue.zetaZeroDivisor_functionalEquationPartner K]
    exact ρ.2⟩
  invFun ρ := ⟨functionalEquationPartner ρ.1, by
    rw [DedekindResidue.zetaZeroDivisor_functionalEquationPartner K]
    exact ρ.2⟩
  left_inv ρ := by
    apply Subtype.ext
    simp [functionalEquationPartner]
  right_inv ρ := by
    apply Subtype.ext
    simp [functionalEquationPartner]

@[simp] theorem zetaZeroPartner_apply (ρ : DedekindResidue.ZetaZeros K) :
    (zetaZeroPartner K ρ).1 = functionalEquationPartner ρ.1 := rfl

@[simp] theorem zetaZeroPartner_multiplicity (ρ : DedekindResidue.ZetaZeros K) :
    DedekindResidue.zetaZeroDivisor K (functionalEquationPartner ρ.1) =
      DedekindResidue.zetaZeroDivisor K ρ.1 :=
  DedekindResidue.zetaZeroDivisor_functionalEquationPartner K ρ.1

/-- Every bounded explicit-formula zero window has nonnegative real contribution. -/
theorem zeroWindow_re_nonneg
    (phi : ℂ → ℂ) (f : ℝ → ℝ)
    (hboundary : PoitouBoundaryIdentification phi f)
    (hfourier : ∀ t, 0 ≤ (𝓕 (complexify f) t).re)
    (hregular : DiffContOnCl ℂ phi (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbounded : BddAbove
      ((norm ∘ phi) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    {W : Set ℂ} (hW : Bornology.IsBounded W) :
    0 ≤ (∑ᶠ z, ((MeromorphicOn.divisor
      (DedekindResidue.completedDedekindZetaEntire K) W) z : ℂ) * phi z).re := by
  classical
  rw [DedekindResidue.finsum_divisor_mul_eq_sum_zetaZeros K phi hW]
  have hterm (ρ : DedekindResidue.ZetaZeros K) :
      0 ≤ (((DedekindResidue.zetaZeroDivisor K ρ.1 : ℂ) * phi ρ.1).re) := by
    have hzero := (DedekindResidue.zetaZeroDivisor_ne_zero_iff K).mp ρ.2
    have hstrip : ρ.1 ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 :=
      DedekindResidue.re_mem_of_completedDedekindZetaEntire_eq_zero K hzero
    have hphi := hboundary.re_nonneg phi f hstrip hfourier hregular hbounded
    have hcast :
        ((DedekindResidue.zetaZeroDivisor K ρ.1 : ℂ) * phi ρ.1).re =
          (DedekindResidue.zetaZeroDivisor K ρ.1 : ℝ) * (phi ρ.1).re := by
      simp [Complex.mul_re]
    rw [hcast]
    exact mul_nonneg
      (by exact_mod_cast DedekindResidue.zetaZeroDivisor_nonneg K ρ.1) hphi
  generalize (DedekindResidue.finite_zetaZeros_mem_of_isBounded K hW).toFinset = S
  induction S using Finset.induction_on with
  | empty => simp
  | @insert ρ S hρ ih =>
      rw [Finset.sum_insert hρ, Complex.add_re]
      exact add_nonneg (hterm ρ) ih

end Odlyzko
