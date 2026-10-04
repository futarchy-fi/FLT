/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierTateGalois
public import FLT.GroupScheme.PDivisibleRationalPlaceTransport
public import FLT.PadicHodgeTheory.ComplexCyclotomicTilt

/-! # The original rational-place Cartier roots in the actual integral tilt -/

@[expose] public noncomputable section
open PadicHodgeTheory
open scoped NNReal
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]

/-- Embed the original algebraic closure in C_p using the fixed original field transport. -/
def rationalPlaceComplexMap :
    AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (rationalPlaceClosureEquiv p).toRingHom

variable {p} {height : ℕ}
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The actual finite Cartier value is an integer in C_p, since its p-power is one. -/
def rationalCartierRoot (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) : 𝓞_ℂ_[p] :=
  ⟨rationalPlaceComplexMap p (X.cartierTatePairing y x n : _), by
    change Valued.v (rationalPlaceComplexMap p (X.cartierTatePairing y x n : _)) ≤
      (1 : ℝ≥0)
    apply (pow_le_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤
      Valued.v (rationalPlaceComplexMap p (X.cartierTatePairing y x n : _)))
      (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
    rw [← map_pow, ← map_pow]
    have h := congrArg Units.val (X.cartierTateLevelPairing_pow n y (X.tateEval n x))
    change (X.cartierTatePairing y x n : AlgebraicClosure
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) ^ (p ^ n) = 1 at h
    rw [h, map_one, map_one]⟩

/-- Original level transitions become literal p-th powers in the actual integer ring. -/
theorem rationalCartierRoot_transition (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    rationalCartierRoot X y x (n + 1) ^ p = rationalCartierRoot X y x n := by
  apply Subtype.ext
  change rationalPlaceComplexMap p (X.cartierTatePairing y x (n + 1) : _) ^ p = _
  rw [← map_pow]
  congr 1
  have h := congrArg Units.val (X.cartierTatePairing_transition (Nat.le_succ n) y x)
  simpa using h

/-- The original Cartier roots form a multiplicative inverse-Frobenius sequence. -/
def rationalCartierRootSequence (y : X.CartierTate) (x : X.tateSequences) :
    Perfection 𝓞_ℂ_[p] p :=
  ⟨rationalCartierRoot X y x, rationalCartierRoot_transition X y x⟩

/-- The zeroth root is one, as required by the original p^0-annihilation law. -/
theorem rationalCartierRoot_zero (y : X.CartierTate) (x : X.tateSequences) :
    rationalCartierRoot X y x 0 = 1 := by
  apply Subtype.ext
  have h := X.cartierTateLevelPairing_pow 0 y (X.tateEval 0 x)
  simp only [pow_zero, pow_one] at h
  change rationalPlaceComplexMap p (X.cartierTatePairing y x 0 : _) = 1
  change X.cartierTatePairing y x 0 = 1 at h
  rw [h]
  exact map_one _

/-- The actual original Cartier roots define an element of the existing integral tilt. -/
def rationalCartierTilt (y : X.CartierTate) (x : X.tateSequences) : IntegralTilt p :=
  Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})
    (rationalCartierRootSequence X y x)

/-- The sharp of this particular Cartier tilt element is one. -/
theorem rationalCartierTilt_sharp (y : X.CartierTate) (x : X.tateSequences) :
    complexSharp p (rationalCartierTilt X y x) = 1 := by
  have h := Perfection.coeff_zero_symm_quotientMulEquiv (rationalCartierTilt X y x)
  rw [rationalCartierTilt, MulEquiv.symm_apply_apply] at h
  exact h.symm.trans (rationalCartierRoot_zero X y x)

end ThreeAdicPlan
