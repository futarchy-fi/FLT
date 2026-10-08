/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleOutputParameter

/-!
# Comparing all three pencils in the left output's parameters

The same invertible change is applied to all three pencils. The left outer
third factor becomes U; the right outer third factor keeps the associativity
minor as its constant homogeneous coefficient. Eliminating the two inner
third factors leaves an exact comparison with all correction terms retained.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- A pencil correction in the common parameters centered at the left outer output. -/
def infinityTripleCenteredPencil (c : Fin 7) (j k : Fin 4)
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  let X := infinityTripleOutputParamX W hΔ 2 U V
  let Y := infinityTripleOutputParamY W hΔ 2 U V
  let l := infinityTripleScalarSlope W hΔ j
  let m := infinityTripleScalarSlope W hΔ k
  let Z := infinityTripleScalarZ W hΔ c * Y
  let E := infinityTripleOutputParamInput W hΔ 2 c U V
  (l - m) * infinityCubicDividedZ A X Y (Z + l * E) (Z + m * E)

/-- The inner pencil retains its two inner third factors in the common parameters. -/
theorem infinityTripleCenteredPencil_inner (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    infinityTripleScalarScale W hΔ 0 * infinityTripleOutputParamInput W hΔ 2 0 U V *
        infinityTripleOutputParamThird W hΔ 2 3 U V -
      infinityTripleScalarScale W hΔ 1 * infinityTripleOutputParamInput W hΔ 2 2 U V *
        infinityTripleOutputParamThird W hΔ 2 4 U V =
      infinityTripleCenteredPencil W hΔ 1 0 1 U V :=
  infinityTripleScalar_inner_pencil_homogeneous W hΔ
    (infinityTripleOutputParamX W hΔ 2 U V) (infinityTripleOutputParamY W hΔ 2 U V)

/-- The left outer pencil has the simple third factor U, without a unit hypothesis on negated Y. -/
theorem infinityTripleCenteredPencil_left (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    infinityTripleScalarScale W hΔ 2 * infinityTripleOutputParamInput W hΔ 2 3 U V * U -
      infinityTripleScalarScale W hΔ 1 * infinityTripleOutputParamInput W hΔ 2 1 U V *
        infinityTripleOutputParamThird W hΔ 2 4 U V =
      infinityTripleCenteredPencil W hΔ 2 2 1 U V := by
  have h := infinityTripleScalar_left_outer_pencil_homogeneous W hΔ
    (infinityTripleOutputParamX W hΔ 2 U V) (infinityTripleOutputParamY W hΔ 2 U V)
  change infinityTripleScalarScale W hΔ 2 * infinityTripleOutputParamInput W hΔ 2 3 U V *
      infinityTripleOutputParamThird W hΔ 2 (infinityTripleOutputIndex 2) U V - _ = _ at h
  rw [infinityTripleOutputParamThird_self] at h
  exact h

/-- The right outer pencil keeps the third factor whose constant term is the outer minor. -/
theorem infinityTripleCenteredPencil_right (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    infinityTripleScalarScale W hΔ 0 * infinityTripleOutputParamInput W hΔ 2 1 U V *
        infinityTripleOutputParamThird W hΔ 2 3 U V -
      infinityTripleScalarScale W hΔ 3 * infinityTripleOutputParamInput W hΔ 2 4 U V *
        infinityTripleOutputParamThird W hΔ 2 6 U V =
      infinityTripleCenteredPencil W hΔ 0 0 3 U V :=
  infinityTripleScalar_right_outer_pencil_homogeneous W hΔ
    (infinityTripleOutputParamX W hΔ 2 U V) (infinityTripleOutputParamY W hΔ 2 U V)

/-- Eliminating both inner third factors preserves the full centered correction. -/
theorem infinityTripleCenteredPencil_outer (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    infinityTripleScalarScale W hΔ 2 * infinityTripleOutputParamInput W hΔ 2 3 U V *
        infinityTripleOutputParamInput W hΔ 2 2 U V * U -
      infinityTripleScalarScale W hΔ 3 * infinityTripleOutputParamInput W hΔ 2 0 U V *
        infinityTripleOutputParamInput W hΔ 2 4 U V *
          infinityTripleOutputParamThird W hΔ 2 6 U V =
      infinityTripleOutputParamInput W hΔ 2 2 U V *
          infinityTripleCenteredPencil W hΔ 2 2 1 U V +
        infinityTripleOutputParamInput W hΔ 2 0 U V *
          infinityTripleCenteredPencil W hΔ 0 0 3 U V -
        infinityTripleOutputParamInput W hΔ 2 1 U V *
          infinityTripleCenteredPencil W hΔ 1 0 1 U V := by
  linear_combination
    infinityTripleOutputParamInput W hΔ 2 2 U V * infinityTripleCenteredPencil_left W hΔ U V +
    infinityTripleOutputParamInput W hΔ 2 0 U V * infinityTripleCenteredPencil_right W hΔ U V -
    infinityTripleOutputParamInput W hΔ 2 1 U V * infinityTripleCenteredPencil_inner W hΔ U V

end FLT.Mazur.WeierstrassIntegralChart
