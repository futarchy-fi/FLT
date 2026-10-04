/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleRationalCartierPeriods
public import FLT.GroupScheme.PDivisibleCartierPairingBilinear
public import FLT.PadicHodgeTheory.ComplexSharpOneLogAdditivity

/-! # Additivity of the actual original root periods in both Tate vectors -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Adding actual dual Tate vectors multiplies their original integral root sequences. -/
theorem rationalCartierRootSequence_add_left (y z : X.CartierTate) (x : X.tateSequences) :
    rationalCartierRootSequence X (y + z) x =
      rationalCartierRootSequence X y x * rationalCartierRootSequence X z x := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  change rationalPlaceComplexMap p (X.cartierTatePairing (y + z) x n : _) =
    rationalPlaceComplexMap p (X.cartierTatePairing y x n : _) *
      rationalPlaceComplexMap p (X.cartierTatePairing z x n : _)
  rw [X.cartierTatePairing_add_left, Units.val_mul, map_mul]

/-- Adding actual Tate vectors multiplies their original integral root sequences. -/
theorem rationalCartierRootSequence_add_right (y : X.CartierTate) (x w : X.tateSequences) :
    rationalCartierRootSequence X y (x + w) =
      rationalCartierRootSequence X y x * rationalCartierRootSequence X y w := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  change rationalPlaceComplexMap p (X.cartierTatePairing y (x + w) n : _) =
    rationalPlaceComplexMap p (X.cartierTatePairing y x n : _) *
      rationalPlaceComplexMap p (X.cartierTatePairing y w n : _)
  rw [X.cartierTatePairing_add_right, Units.val_mul, map_mul]

/-- The actual tilt construction respects dual Tate addition. -/
theorem rationalCartierTilt_add_left (y z : X.CartierTate) (x : X.tateSequences) :
    rationalCartierTilt X (y + z) x = rationalCartierTilt X y x * rationalCartierTilt X z x := by
  rw [rationalCartierTilt, rationalCartierRootSequence_add_left, map_mul]
  rfl

/-- The actual tilt construction respects Tate addition. -/
theorem rationalCartierTilt_add_right (y : X.CartierTate) (x w : X.tateSequences) :
    rationalCartierTilt X y (x + w) = rationalCartierTilt X y x * rationalCartierTilt X y w := by
  rw [rationalCartierTilt, rationalCartierRootSequence_add_right, map_mul]
  rfl

/-- The original logarithmic period is additive in its actual dual Tate vector. -/
theorem rationalCartierPeriod_add_left (y z : X.CartierTate) (x : X.tateSequences) :
    rationalCartierPeriod X (y + z) x =
      rationalCartierPeriod X y x + rationalCartierPeriod X z x := by
  unfold rationalCartierPeriod
  simp only [rationalCartierTilt_add_left]
  exact complexTiltLog_mul p _ _ (rationalCartierTilt_sharp X y x) (rationalCartierTilt_sharp X z x)

/-- The original logarithmic period is additive in its actual Tate vector. -/
theorem rationalCartierPeriod_add_right (y : X.CartierTate) (x w : X.tateSequences) :
    rationalCartierPeriod X y (x + w) =
      rationalCartierPeriod X y x + rationalCartierPeriod X y w := by
  unfold rationalCartierPeriod
  simp only [rationalCartierTilt_add_right]
  exact complexTiltLog_mul p _ _ (rationalCartierTilt_sharp X y x) (rationalCartierTilt_sharp X y w)

/-- The actual period pairing as a homomorphism in both original Tate vectors. -/
def rationalCartierPeriodHom : X.CartierTate →+ (X.tateSequences →+ ComplexBDeRhamPlus p) where
  toFun y :=
    { toFun := rationalCartierPeriod X y
      map_zero' := by
        have h := rationalCartierPeriod_add_right X y 0 0
        rw [add_zero] at h
        exact add_eq_left.mp h.symm
      map_add' := rationalCartierPeriod_add_right X y }
  map_zero' := by
    ext x
    have h := rationalCartierPeriod_add_left X 0 0 x
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  map_add' y z := by
    ext x
    exact rationalCartierPeriod_add_left X y z x

end ThreeAdicPlan
