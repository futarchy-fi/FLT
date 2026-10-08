/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityDenominatorShift
public import FLT.Mazur.WeierstrassInfinityTriplePolynomials

/-!
# Actual cross denominators and their unit combinations

At either endpoint of a genuine addition law, compare its actual line with a
line of any of the other three slopes. The chosen slope denominator is an
explicit combination of this cross denominator and the input displacement.
Reversing endpoints does not silently assert that the reversed denominator is a unit.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The cross denominator at the right endpoint, comparing another slope through the left. -/
def infinityTripleForwardCrossDenominator (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  let x := infinityTripleScalarX W hΔ
  let z := infinityTripleScalarZ W hΔ
  let a := infinityTripleLeftIndex j
  let b := infinityTripleRightIndex j
  infinitySlopeDenominator A (x b)
    (z a + infinityTripleScalarSlope W hΔ k * (x b - x a)) (z b)

/-- The cross denominator at the left endpoint, with comparison line through the right. -/
def infinityTripleReverseCrossDenominator (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  let x := infinityTripleScalarX W hΔ
  let z := infinityTripleScalarZ W hΔ
  let a := infinityTripleLeftIndex j
  let b := infinityTripleRightIndex j
  infinitySlopeDenominator A (x a)
    (z b + infinityTripleScalarSlope W hΔ k * (x a - x b)) (z a)

/-- Exact comparison at the forward endpoint with the genuine chosen denominator. -/
theorem infinityTripleForwardCrossDenominator_corrected (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    let l := infinityTripleScalarSlope W hΔ k
    let d := x b - x a
    infinityTripleForwardCrossDenominator W hΔ j k -
        d * (l * infinityDenominatorShiftFactor A (x b) (z a) (z b) (l * d)) =
      infinitySlopeDenominator A (x b) (z a) (z b) :=
  infinitySlopeDenominator_cross_shift _ _ _ _ _ _

/-- The forward cross denominator and displacement have a unit linear combination. -/
theorem infinityTripleForwardCrossDenominator_unit (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    let l := infinityTripleScalarSlope W hΔ k
    let d := x b - x a
    IsUnit (infinityTripleForwardCrossDenominator W hΔ j k -
      d * (l * infinityDenominatorShiftFactor A (x b) (z a) (z b) (l * d))) := by
  dsimp only
  rw [infinityTripleForwardCrossDenominator_corrected]
  exact infinityTripleScalar_den_unit W hΔ j

/-- Exact reversal comparison retains the original denominator's X argument. -/
theorem infinityTripleReverseCrossDenominator_corrected (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    let l := infinityTripleScalarSlope W hΔ k
    let d := x a - x b
    infinityTripleReverseCrossDenominator W hΔ j k -
        d * infinityDenominatorEndpointShift A (x b) (z b) (z a) l d =
      infinitySlopeDenominator A (x b) (z a) (z b) := by
  dsimp only
  have h := infinitySlopeDenominator_endpoint_shift
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤)))
    (infinityTripleScalarX W hΔ (infinityTripleRightIndex j))
    (infinityTripleScalarZ W hΔ (infinityTripleRightIndex j))
    (infinityTripleScalarZ W hΔ (infinityTripleLeftIndex j))
    (infinityTripleScalarSlope W hΔ k)
    (infinityTripleScalarX W hΔ (infinityTripleLeftIndex j) -
      infinityTripleScalarX W hΔ (infinityTripleRightIndex j))
  rw [← add_sub_assoc, add_sub_cancel_left] at h
  unfold infinityTripleReverseCrossDenominator
  rw [h]
  unfold infinitySlopeDenominator
  ring

/-- The reverse cross denominator and reversed displacement also have a unit combination. -/
theorem infinityTripleReverseCrossDenominator_unit (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    let l := infinityTripleScalarSlope W hΔ k
    let d := x a - x b
    IsUnit (infinityTripleReverseCrossDenominator W hΔ j k -
      d * infinityDenominatorEndpointShift A (x b) (z b) (z a) l d) := by
  dsimp only
  rw [infinityTripleReverseCrossDenominator_corrected]
  exact infinityTripleScalar_den_unit W hΔ j

end FLT.Mazur.WeierstrassIntegralChart
