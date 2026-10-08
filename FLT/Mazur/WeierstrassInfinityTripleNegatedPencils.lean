/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleLineResidual
public import FLT.Mazur.WeierstrassInfinityHomogeneousPencil

/-!
# The three genuine pencils evaluated at negated outputs

The homogeneous pencils now give a linear system in the actual negated-point
minors. Evaluation requires no invertibility of a negated Y coordinate.
The left output makes the left outer third factor vanish identically.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- An input factor evaluated at the negation of an actual point. -/
def infinityTripleNegInputFactor (i k : Fin 7) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarX W hΔ i - infinityTripleScalarX W hΔ k * infinityTripleNegY W hΔ i

/-- A homogeneous pencil correction evaluated at an actual negated point. -/
def infinityTripleNegPencilValue (i c : Fin 7) (j k : Fin 4) :
    Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  let l := infinityTripleScalarSlope W hΔ j
  let m := infinityTripleScalarSlope W hΔ k
  let n := infinityTripleNegY W hΔ i
  let Z := infinityTripleScalarZ W hΔ c * n
  (l - m) * infinityCubicDividedZ A (infinityTripleScalarX W hΔ i) n
    (Z + l * infinityTripleNegInputFactor W hΔ i c)
    (Z + m * infinityTripleNegInputFactor W hΔ i c)

/-- The inner pencil becomes an exact linear relation between two genuine minors. -/
theorem infinityTripleNegPencil_inner (i : Fin 7) :
    infinityTripleScalarScale W hΔ 0 * infinityTripleNegInputFactor W hΔ i 0 *
        infinityTripleNegMinor W hΔ 3 i -
      infinityTripleScalarScale W hΔ 1 * infinityTripleNegInputFactor W hΔ i 2 *
        infinityTripleNegMinor W hΔ 4 i = infinityTripleNegPencilValue W hΔ i 1 0 1 :=
  infinityTripleScalar_inner_pencil_homogeneous W hΔ
    (infinityTripleScalarX W hΔ i) (infinityTripleNegY W hΔ i)

/-- The left outer pencil becomes an exact linear relation in the same minors. -/
theorem infinityTripleNegPencil_left (i : Fin 7) :
    infinityTripleScalarScale W hΔ 2 * infinityTripleNegInputFactor W hΔ i 3 *
        infinityTripleNegMinor W hΔ 5 i -
      infinityTripleScalarScale W hΔ 1 * infinityTripleNegInputFactor W hΔ i 1 *
        infinityTripleNegMinor W hΔ 4 i = infinityTripleNegPencilValue W hΔ i 2 2 1 :=
  infinityTripleScalar_left_outer_pencil_homogeneous W hΔ
    (infinityTripleScalarX W hΔ i) (infinityTripleNegY W hΔ i)

/-- The right outer pencil contains precisely the remaining outer minor. -/
theorem infinityTripleNegPencil_right (i : Fin 7) :
    infinityTripleScalarScale W hΔ 0 * infinityTripleNegInputFactor W hΔ i 1 *
        infinityTripleNegMinor W hΔ 3 i -
      infinityTripleScalarScale W hΔ 3 * infinityTripleNegInputFactor W hΔ i 4 *
        infinityTripleNegMinor W hΔ 6 i = infinityTripleNegPencilValue W hΔ i 0 0 3 :=
  infinityTripleScalar_right_outer_pencil_homogeneous W hΔ
    (infinityTripleScalarX W hΔ i) (infinityTripleNegY W hΔ i)

/-- A point's minor with itself vanishes over the common section ring. -/
@[simp] theorem infinityTripleNegMinor_self (i : Fin 7) :
    infinityTripleNegMinor W hΔ i i = 0 := by
  unfold infinityTripleNegMinor
  ring

/-- Reversing a pair reverses its homogeneous minor. -/
theorem infinityTripleNegMinor_swap (i k : Fin 7) :
    infinityTripleNegMinor W hΔ i k = -infinityTripleNegMinor W hΔ k i := by
  unfold infinityTripleNegMinor
  ring

/-- At the left output its own third factor disappears, with no scalar cancellation. -/
theorem infinityTripleNegPencil_left_at_left :
    -(infinityTripleScalarScale W hΔ 1 * infinityTripleNegInputFactor W hΔ 5 1 *
      infinityTripleNegMinor W hΔ 4 5) = infinityTripleNegPencilValue W hΔ 5 2 2 1 := by
  simpa only [infinityTripleNegMinor_self, mul_zero, zero_sub] using
    infinityTripleNegPencil_left W hΔ 5

/-- The opposite pencil exposes the oriented associativity minor at the left output. -/
theorem infinityTripleNegPencil_right_at_left :
    infinityTripleScalarScale W hΔ 0 * infinityTripleNegInputFactor W hΔ 5 1 *
        infinityTripleNegMinor W hΔ 3 5 +
      infinityTripleScalarScale W hΔ 3 * infinityTripleNegInputFactor W hΔ 5 4 *
        infinityTripleNegMinor W hΔ 5 6 = infinityTripleNegPencilValue W hΔ 5 0 0 3 := by
  have h := infinityTripleNegPencil_right W hΔ 5
  rw [infinityTripleNegMinor_swap W hΔ 6 5] at h
  linear_combination h

end FLT.Mazur.WeierstrassIntegralChart
