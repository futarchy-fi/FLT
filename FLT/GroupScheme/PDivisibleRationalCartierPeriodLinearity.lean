/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleRationalCartierPeriodAdditivity
public import FLT.GroupScheme.PDivisibleCartierPairingScalars
public import FLT.PadicHodgeTheory.ComplexRootLogLinearity

/-! # P-adic bilinearity of the actual original Cartier period values -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The original logarithmic period is linear in the original Tate vector over Z_p. -/
theorem rationalCartierPeriod_padic_smul_right (a : ℤ_[p])
    (y : X.CartierTate) (x : X.tateSequences) :
    rationalCartierPeriod X y (a • x) =
      complexPadicToDeRham p (a : ℚ_[p]) * rationalCartierPeriod X y x := by
  apply complexRootSequenceLog_padic p (rationalCartierRootSequence X y x)
    (rationalCartierRootSequence X y (a • x))
    (rationalCartierRoot_zero X y x) (rationalCartierRoot_zero X y (a • x)) a
  intro n
  apply Subtype.ext
  change rationalPlaceComplexMap p (X.cartierTatePairing y (a • x) n : _) =
    rationalPlaceComplexMap p (X.cartierTatePairing y x n : _) ^ (PadicInt.toZModPow n a).val
  rw [X.cartierTatePairing_padic_smul_right, Units.val_pow_eq_pow_val, map_pow]

/-- P-adic scalars can be transferred between the two actual Tate arguments. -/
theorem rationalCartierPeriod_padic_balanced (a : ℤ_[p])
    (y : X.CartierTate) (x : X.tateSequences) :
    rationalCartierPeriod X (a • y) x = rationalCartierPeriod X y (a • x) :=
  rationalCartierPeriod_ext X _ _ _ _ (X.cartierTatePairing_padic_balanced a y x)

/-- The same period is linear in the original dual Tate vector over Z_p. -/
theorem rationalCartierPeriod_padic_smul_left (a : ℤ_[p])
    (y : X.CartierTate) (x : X.tateSequences) :
    rationalCartierPeriod X (a • y) x =
      complexPadicToDeRham p (a : ℚ_[p]) * rationalCartierPeriod X y x := by
  rw [rationalCartierPeriod_padic_balanced, rationalCartierPeriod_padic_smul_right]

/-- The existing p-adic period embedding restricted to the integral p-adic scalars. -/
def rationalCartierPeriodScalars : ℤ_[p] →+* ComplexBDeRhamPlus p :=
  (complexPadicToDeRham p).comp (algebraMap ℤ_[p] ℚ_[p])

/-- The actual period construction as a map linear in both original p-adic Tate modules. -/
def rationalCartierPeriodBilinear :
    X.CartierTate →ₛₗ[rationalCartierPeriodScalars (p := p)]
      (X.tateSequences →ₛₗ[rationalCartierPeriodScalars (p := p)] ComplexBDeRhamPlus p) where
  toFun y :=
    { __ := rationalCartierPeriodHom X y
      map_smul' a x := rationalCartierPeriod_padic_smul_right X a y x }
  map_add' y z := by
    apply LinearMap.ext
    intro x
    exact rationalCartierPeriod_add_left X y z x
  map_smul' a y := by
    apply LinearMap.ext
    intro x
    exact rationalCartierPeriod_padic_smul_left X a y x

/-- The bilinear map evaluates to the period of the originally specified Cartier root sequence. -/
theorem rationalCartierPeriodBilinear_apply (y : X.CartierTate) (x : X.tateSequences) :
    rationalCartierPeriodBilinear X y x = rationalCartierPeriod X y x := rfl

end ThreeAdicPlan
