/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTriplePencilEndpoints
public import Mathlib.RingTheory.Ideal.Span

/-!
# Exact endpoint ideals for the three pencils

The cross denominators are units modulo the corresponding input displacement.
Consequently each endpoint product and the corresponding slope difference
generate the same ideal together with that displacement. These statements use
the original denominator units and hold on the entire true triple member.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

/-- A coefficient invertible modulo a displacement can be removed from a two-generator ideal. -/
theorem infinity_cross_denominator_span {S : Type*} [CommRing S]
    (d D h r p : S) (hu : IsUnit (D - d * h)) (hp : p = r * D) :
    Ideal.span ({d, p} : Set S) = Ideal.span ({d, r} : Set S) := by
  have he : p - d * (r * h) = r * (D - d * h) := by
    rw [hp]
    ring
  calc
    _ = Ideal.span ({d, p - d * (r * h)} : Set S) :=
      (Ideal.span_pair_sub_left_mul d p (r * h)).symm
    _ = Ideal.span ({d, r * (D - d * h)} : Set S) := by rw [he]
    _ = _ := by
      rw [Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_mul_right_unit hu]

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The genuine forward cross denominator can be removed modulo the input displacement. -/
theorem infinityTripleForwardCrossDenominator_span (j k : Fin 4)
    (r : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let d := infinityTripleScalarX W hΔ (infinityTripleRightIndex j) -
      infinityTripleScalarX W hΔ (infinityTripleLeftIndex j)
    Ideal.span ({d, r * infinityTripleForwardCrossDenominator W hΔ j k} :
      Set Γ(InfinityTripleFull W hΔ, ⊤)) = Ideal.span {d, r} := by
  exact infinity_cross_denominator_span _ _ _ _ _
    (infinityTripleForwardCrossDenominator_unit W hΔ j k) rfl

/-- Reversal has the same ideal cancellation with its own signed displacement. -/
theorem infinityTripleReverseCrossDenominator_span (j k : Fin 4)
    (r : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let d := infinityTripleScalarX W hΔ (infinityTripleLeftIndex j) -
      infinityTripleScalarX W hΔ (infinityTripleRightIndex j)
    Ideal.span ({d, r * infinityTripleReverseCrossDenominator W hΔ j k} :
      Set Γ(InfinityTripleFull W hΔ, ⊤)) = Ideal.span {d, r} := by
  exact infinity_cross_denominator_span _ _ _ _ _
    (infinityTripleReverseCrossDenominator_unit W hΔ j k) rfl

/-- The inner point product and inner slope difference give the same displacement ideal. -/
theorem infinityTriplePencilEndpoint_inner_span :
    let x := infinityTripleScalarX W hΔ
    Ideal.span ({x 2 - x 1, infinityTripleScalarScale W hΔ 0 * (x 2 - x 0) *
      (infinityTripleNegY W hΔ 3 * x 2 - x 3)} : Set Γ(InfinityTripleFull W hΔ, ⊤)) =
      Ideal.span {x 2 - x 1,
        infinityTripleScalarSlope W hΔ 0 - infinityTripleScalarSlope W hΔ 1} := by
  dsimp only
  rw [infinityTriplePencilEndpoint_inner]
  exact infinityTripleForwardCrossDenominator_span W hΔ 1 0 _

/-- The left endpoint retains its inner point product and the two actual slopes. -/
theorem infinityTriplePencilEndpoint_left_span :
    let x := infinityTripleScalarX W hΔ
    Ideal.span ({x 3 - x 2, infinityTripleScalarScale W hΔ 1 * (x 3 - x 1) *
      (infinityTripleNegY W hΔ 4 * x 3 - x 4)} : Set Γ(InfinityTripleFull W hΔ, ⊤)) =
      Ideal.span {x 3 - x 2,
        infinityTripleScalarSlope W hΔ 2 - infinityTripleScalarSlope W hΔ 1} := by
  dsimp only
  rw [← Ideal.span_pair_neg, infinityTriplePencilEndpoint_left]
  exact infinityTripleReverseCrossDenominator_span W hΔ 2 1 _

/-- The right endpoint relates the other inner point product to the outer slope difference. -/
theorem infinityTriplePencilEndpoint_right_span :
    let x := infinityTripleScalarX W hΔ
    Ideal.span ({x 4 - x 0, infinityTripleScalarScale W hΔ 0 * (x 4 - x 1) *
      (infinityTripleNegY W hΔ 3 * x 4 - x 3)} : Set Γ(InfinityTripleFull W hΔ, ⊤)) =
      Ideal.span {x 4 - x 0,
        infinityTripleScalarSlope W hΔ 0 - infinityTripleScalarSlope W hΔ 3} := by
  dsimp only
  rw [infinityTriplePencilEndpoint_right]
  exact infinityTripleForwardCrossDenominator_span W hΔ 3 0 _

end FLT.Mazur.WeierstrassIntegralChart
