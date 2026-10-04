/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleRationalPlaceTransport
public import FLT.PadicHodgeTheory.ComplexThickeningTransitions

/-! # Integral thickenings over the original rational-place base -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]

/-- The original rational-place base acts through its specified Z_p identification. -/
instance rationalPlaceAinfAlgebra :
    Algebra ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) (Ainf p) :=
  ((complexPadicIntToAinf p).comp (rationalPlaceIntegersEquiv p).toRingEquiv.toRingHom).toAlgebra

/-- The corresponding actual integral residue coefficients, before reducing modulo p. -/
instance rationalPlaceComplexIntegerAlgebra :
    Algebra ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) 𝓞_ℂ_[p] :=
  ((complexPadicIntToInteger p).comp
    (rationalPlaceIntegersEquiv p).toRingEquiv.toRingHom).toAlgebra

/-- Theta respects the original integral base, not just the abstract prime field. -/
def rationalPlaceTheta : Ainf p →ₐ[
    (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] 𝓞_ℂ_[p] :=
  { complexTheta p with commutes' := fun _ ↦ complexPadicIntToAinf_theta p _ }

/-- The actual integral coefficient reduction as an algebra map over the original base. -/
def rationalPlaceThickeningTheta (r s : ℕ) (hr : 0 < r) :
    ComplexIntegralThickening p r s →ₐ[
      (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] ComplexIntegerModPow p s :=
  { complexThickeningTheta p r s hr with
    commutes' := fun _ ↦ congrArg (Ideal.Quotient.mk _) (complexPadicIntToAinf_theta p _) }

/-- All integral precision reductions respect that same base. -/
def rationalPlaceThickeningReduce {r r' s s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    ComplexIntegralThickening p r' s' →ₐ[
      (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
        ComplexIntegralThickening p r s :=
  { complexThickeningReduce p hr hs with commutes' := fun _ ↦ rfl }

/-- The residue precision map with its original-base algebra structure. -/
def rationalPlaceIntegerModPowReduce {s s' : ℕ} (hs : s ≤ s') :
    ComplexIntegerModPow p s' →ₐ[
      (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] ComplexIntegerModPow p s :=
  { complexIntegerModPowReduce p hs with commutes' := fun _ ↦ rfl }

/-- The square of actual original-base coefficient maps commutes. -/
theorem rationalPlaceThickeningTheta_reduce {r r' s s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') (hr₀ : 0 < r) :
    (rationalPlaceThickeningTheta p r s hr₀).comp (rationalPlaceThickeningReduce p hr hs) =
      (rationalPlaceIntegerModPowReduce p hs).comp
        (rationalPlaceThickeningTheta p r' s' (hr₀.trans_le hr)) :=
  AlgHom.coe_ringHom_injective (complexThickeningTheta_reduce p hr hs hr₀)

/-- The reduction kernel is killed by the actual p-power precision. -/
theorem rationalPlaceThickeningTheta_kernel_smul (r s : ℕ) (hr : 0 < r)
    (a : RingHom.ker (rationalPlaceThickeningTheta p r s hr)) : p ^ s • a = 0 := by
  apply Subtype.ext
  change p ^ s • (a : ComplexIntegralThickening p r s) = 0
  rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul]

end ThreeAdicPlan
