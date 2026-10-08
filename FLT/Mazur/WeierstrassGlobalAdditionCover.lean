/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveProduct
public import FLT.Mazur.WeierstrassInputAdditionCovers
public import FLT.Mazur.WeierstrassAffineAdditionGluing

/-!
# Regular local laws covering the entire integral curve product

Refine the actual Y/Z product atlas by the already constructed addition-domain
covers. Every member has its existing regular law into the glued cubic.
Compatibility across this global cover is a separate obligation; this module
does not assume or assert it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The regular addition-domain refinement on each concrete input tensor chart. -/
def integralInputAdditionCover (b c : Bool) :
    (Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))).OpenCover :=
  match b, c with
  | true, true => yProductAdditionCover W hΔ
  | true, false => mixedProductAdditionCover W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl)
  | false, true => mixedProductAdditionCover W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl)
  | false, false => mixedProductAdditionCover W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl)

/-- Each member retains its existing regular local addition into the global target. -/
def integralInputAdditionLocal (b c : Bool) (i : (integralInputAdditionCover W hΔ b c).I₀) :
    (integralInputAdditionCover W hΔ b c).X i ⟶ integralCurve W := by
  cases b <;> cases c
  · exact mixedProductAdditionSpec W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl) i ≫
      integralCurveChart W (mixedProductAdditionOutput W hΔ 2 2
        (.inr rfl) (.inr rfl) (.inl rfl) i)
  · exact mixedProductAdditionSpec W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl) i ≫
      integralCurveChart W (mixedProductAdditionOutput W hΔ 2 1
        (.inr rfl) (.inl rfl) (.inl rfl) i)
  · exact mixedProductAdditionSpec W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl) i ≫
      integralCurveChart W (mixedProductAdditionOutput W hΔ 1 2
        (.inl rfl) (.inr rfl) (.inr rfl) i)
  · exact yProductAdditionSpec W hΔ i ≫ integralCurveChart W (yProductAdditionOutput W hΔ i)

/-- An actual open cover of the full fiber product carrying all local addition laws. -/
def integralCurveAdditionCover : (integralCurveProduct W).OpenCover :=
  (integralCurveProductCover W).bind (fun p => integralInputAdditionCover W hΔ p.1 p.2)

/-- The existing regular laws on every member of the full product cover. -/
def integralCurveAdditionLocal (i : (integralCurveAdditionCover W hΔ).I₀) :
    (integralCurveAdditionCover W hΔ).X i ⟶ integralCurve W :=
  integralInputAdditionLocal W hΔ i.1.1 i.1.2 i.2

/-- Every point of the actual product belongs to a domain with a constructed local law. -/
theorem integralCurveAdditionCover_covers (x : integralCurveProduct W) :
    ∃ (i : (integralCurveAdditionCover W hΔ).I₀)
      (y : (integralCurveAdditionCover W hΔ).X i),
      (integralCurveAdditionCover W hΔ).f i y = x :=
  (integralCurveAdditionCover W hΔ).exists_eq x

end FLT.Mazur.WeierstrassIntegralChart
