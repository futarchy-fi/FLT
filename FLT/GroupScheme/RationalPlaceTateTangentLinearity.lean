/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateTangentAdditivity
public import FLT.GroupScheme.PadicTorsionScalarContinuity

/-! # P-adic linearity of the constructed original Tate tangent -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- At precision s the cotangent functional depends only on the original level-s Tate coordinate. -/
theorem rationalPlaceTateCotangentFunctional_eq_of_eval (s : ℕ) (x z : X.tateSequences)
    (h : X.tateEval s x = X.tateEval s z) :
    rationalPlaceTateCotangentFunctional X s x = rationalPlaceTateCotangentFunctional X s z := by
  rw [rationalPlaceTateCotangentFunctional_at, rationalPlaceTateCotangentFunctional_at]
  have he : rationalPlaceTateInfinitesimalAt X s x = rationalPlaceTateInfinitesimalAt X s z := by
    apply Subtype.ext
    exact congrArg (fun v ↦ X.squareZeroLevelLift
      (rationalPlaceThickeningTheta p 2 s (by decide))
      (complexThickeningTheta_surjective p 2 s (by decide))
      (complexThickeningTheta_ker_pow p 2 s (by decide)) (p ^ s)
      (fun b _ ↦ by
        rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul]) s
      ((rationalPlaceIntegralModPow p s).comp ((X.level s).integralPointCoordinate v))) h
  rw [he]

/-- Every kernel-valued cotangent functional is killed by the actual coefficient precision. -/
theorem rationalPlaceCotangentFunctional_pow_smul (s : ℕ)
    (f : X.cotangentLimit →ₗ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
      RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide))) : p ^ s • f = 0 := by
  ext v
  change p ^ s • (f v : ComplexIntegralThickening p 2 s) = 0
  rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul]

/-- Original p-adic scalars act through the specified integral base identification. -/
theorem rationalPlaceTateCotangentFunctional_smul (s : ℕ) (a : ℤ_[p]) (x : X.tateSequences) :
    rationalPlaceTateCotangentFunctional X s (a • x) =
      (rationalPlaceIntegersEquiv p).symm a • rationalPlaceTateCotangentFunctional X s x := by
  let k := (PadicInt.toZModPow s a).val
  have he : X.tateEval s (a • x) = X.tateEval s (k • x) := by
    change X.tateEvalLinear s (a • x) = X.tateEvalLinear s (k • x)
    rw [map_smul, map_nsmul, X.padic_smul_points,
      ← ZMod.natCast_zmod_val (PadicInt.toZModPow s a), Nat.cast_smul_eq_nsmul]
  have hs := torsion_smul_eq_of_padic_residue (rationalPlaceIntegersEquiv p).toRingEquiv s
    (rationalPlaceCotangentFunctional_pow_smul X s)
    (a := a) (b := (k : ℤ_[p])) (by simp [k]) (rationalPlaceTateCotangentFunctional X s x)
  rw [rationalPlaceTateCotangentFunctional_eq_of_eval X s _ _ he]
  change rationalPlaceTateCotangentAddHom X s (k • x) = _
  rw [map_nsmul]
  simp only [map_natCast, Nat.cast_smul_eq_nsmul] at hs
  exact hs.symm

/-- The actual cotangent assignment is semilinear over the original integral base. -/
def rationalPlaceTateCotangentLinear (s : ℕ) :
    X.tateSequences →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom]
      (X.cotangentLimit →ₗ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
        RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide))) where
  __ := rationalPlaceTateCotangentAddHom X s
  map_smul' := rationalPlaceTateCotangentFunctional_smul X s

/-- The original integral tangent tensor is p-adic linear in its actual Tate input. -/
theorem rationalPlaceTateTangentTensor_smul (s : ℕ) (a : ℤ_[p]) (x : X.tateSequences) :
    rationalPlaceTateTangentTensor X s (a • x) =
      (rationalPlaceIntegersEquiv p).symm a • rationalPlaceTateTangentTensor X s x := by
  let e := X.integralTangentCoefficientsEquiv (M := RingHom.ker
    (rationalPlaceThickeningTheta p 2 s (by decide))) (rationalPlaceIntegersEquiv p).toRingEquiv
  apply e.injective
  exact (rationalPlaceTateTangentTensor_pairing X s (a • x)).trans
    ((rationalPlaceTateCotangentFunctional_smul X s a x).trans
      ((congrArg ((rationalPlaceIntegersEquiv p).symm a • ·)
        (rationalPlaceTateTangentTensor_pairing X s x).symm).trans (e.map_smul _ _).symm))

/-- The linear tensor assignment is precisely the tangent tensor already constructed from lifts. -/
def rationalPlaceTateTangentLinear (s : ℕ) :
    X.tateSequences →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom]
      X.IntegralTangent ⊗[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
        RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide)) where
  toFun := rationalPlaceTateTangentTensor X s
  map_add' := rationalPlaceTateTangentTensor_add X s
  map_smul' := rationalPlaceTateTangentTensor_smul X s

end ThreeAdicPlan
