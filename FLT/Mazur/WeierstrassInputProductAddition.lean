/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalAdditionCover
public import FLT.Mazur.WeierstrassYProductAdditionGluing
public import FLT.Mazur.WeierstrassMixedProductAdditionGluing

/-!
# Addition on each chart of the actual curve product

The full local addition refinement descends separately over each of the four
input products. Within a fixed input chart its laws agree even when compared
over the actual global product. Cross-input-chart descent remains separate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The regular curve-valued addition on each of the four Y/Z input products. -/
def integralInputAdditionToCurve (b c : Bool) :
    Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))) ⟶
      integralCurve W :=
  match b, c with
  | true, true => yProductAdditionToCurve W hΔ
  | true, false => mixedProductAdditionToCurve W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl)
  | false, true => mixedProductAdditionToCurve W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl)
  | false, false => mixedProductAdditionToCurve W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl)

/-- The new input-product maps retain every local law of the global refinement. -/
theorem integralInputAdditionLocal_glued (b c : Bool)
    (i : (integralInputAdditionCover W hΔ b c).I₀) :
    (integralInputAdditionCover W hΔ b c).f i ≫ integralInputAdditionToCurve W hΔ b c =
      integralInputAdditionLocal W hΔ b c i := by
  cases b <;> cases c
  · exact mixedProductCurveLocal_glued W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl) i
  · exact mixedProductCurveLocal_glued W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl) i
  · exact mixedProductCurveLocal_glued W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl) i
  · exact yProductCurveLocal_glued W hΔ i

/-- Local laws in a fixed input product agree when their global inputs agree. -/
theorem integralCurveAdditionLocal_sameInput (b c : Bool)
    (i j : (integralInputAdditionCover W hΔ b c).I₀) {X : Scheme.{u}}
    (f : X ⟶ (integralInputAdditionCover W hΔ b c).X i)
    (g : X ⟶ (integralInputAdditionCover W hΔ b c).X j)
    (h : f ≫ (integralCurveAdditionCover W hΔ).f ⟨(b, c), i⟩ =
      g ≫ (integralCurveAdditionCover W hΔ).f ⟨(b, c), j⟩) :
    f ≫ integralCurveAdditionLocal W hΔ ⟨(b, c), i⟩ =
      g ≫ integralCurveAdditionLocal W hΔ ⟨(b, c), j⟩ := by
  have hi : f ≫ (integralInputAdditionCover W hΔ b c).f i =
      g ≫ (integralInputAdditionCover W hΔ b c).f j := by
    apply (cancel_mono (integralCurveProductChart W b c)).mp
    change f ≫ ((integralInputAdditionCover W hΔ b c).f i ≫
      integralCurveProductChart W b c) =
      g ≫ ((integralInputAdditionCover W hΔ b c).f j ≫ integralCurveProductChart W b c) at h
    simpa only [Category.assoc] using h
  change f ≫ integralInputAdditionLocal W hΔ b c i =
    g ≫ integralInputAdditionLocal W hΔ b c j
  rw [← integralInputAdditionLocal_glued, ← integralInputAdditionLocal_glued,
    ← Category.assoc, hi, Category.assoc]

end FLT.Mazur.WeierstrassIntegralChart
