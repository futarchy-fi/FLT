/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTransportedOutputRegular

/-!
# Chart presentations of every actual local addition

Expose the output chart already used in the global addition cover. Its Z
coordinate is regular on every flat restriction, including transported
reciprocal domains and the genuine infinity domain.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The output coordinate of the local law on an input chart. -/
def integralInputAdditionOutput (b c : Bool)
    (i : (integralInputAdditionCover W hΔ b c).I₀) : Fin 3 := by
  cases b <;> cases c
  · exact mixedProductAdditionOutput W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl) i
  · exact mixedProductAdditionOutput W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl) i
  · exact mixedProductAdditionOutput W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl) i
  · exact yProductAdditionOutput W hΔ i

/-- The already constructed local law before its open inclusion into the curve. -/
def integralInputAdditionSpec (b c : Bool)
    (i : (integralInputAdditionCover W hΔ b c).I₀) :
    (integralInputAdditionCover W hΔ b c).X i ⟶
      chartScheme W (integralInputAdditionOutput W hΔ b c i) := by
  cases b <;> cases c
  · exact mixedProductAdditionSpec W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl) i
  · exact mixedProductAdditionSpec W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl) i
  · exact mixedProductAdditionSpec W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl) i
  · exact yProductAdditionSpec W hΔ i

/-- The chart presentation recovers the original curve-valued local law. -/
theorem integralInputAdditionSpec_local (b c : Bool)
    (i : (integralInputAdditionCover W hΔ b c).I₀) :
    integralInputAdditionSpec W hΔ b c i ≫
        integralCurveChart W (integralInputAdditionOutput W hΔ b c i) =
      integralInputAdditionLocal W hΔ b c i := by
  cases b <;> cases c <;> rfl

/-- Output chart of a member of the actual global addition cover. -/
def integralCurveAdditionOutput (i : (integralCurveAdditionCover W hΔ).I₀) : Fin 3 :=
  integralInputAdditionOutput W hΔ i.1.1 i.1.2 i.2

/-- Chart-valued version of the actual global local law. -/
def integralCurveAdditionSpec (i : (integralCurveAdditionCover W hΔ).I₀) :
    (integralCurveAdditionCover W hΔ).X i ⟶ chartScheme W (integralCurveAdditionOutput W hΔ i) :=
  integralInputAdditionSpec W hΔ i.1.1 i.1.2 i.2

/-- The exposed chart presentation is the original local output. -/
theorem integralCurveAdditionSpec_local (i : (integralCurveAdditionCover W hΔ).I₀) :
    integralCurveAdditionSpec W hΔ i ≫
        integralCurveChart W (integralCurveAdditionOutput W hΔ i) =
      integralCurveAdditionLocal W hΔ i :=
  integralInputAdditionSpec_local W hΔ i.1.1 i.1.2 i.2

/-- All actual local output Z coordinates remain regular under flat restriction. -/
theorem integralCurveAdditionSpec_z_regular (i : (integralCurveAdditionCover W hΔ).I₀)
    {X : Scheme.{u}} (f : X ⟶ (integralCurveAdditionCover W hΔ).X i) [Flat f] :
    IsRegular (specSectionHom (f ≫ integralCurveAdditionSpec W hΔ i)
      (coord W (integralCurveAdditionOutput W hΔ i) 2)) := by
  rcases i with ⟨⟨b, c⟩, i⟩
  cases b <;> cases c
  · exact mixedProductAdditionSpec_z_regular W hΔ 2 2
      (.inr rfl) (.inr rfl) (.inl rfl) i f
  · exact mixedProductAdditionSpec_z_regular W hΔ 2 1
      (.inr rfl) (.inl rfl) (.inl rfl) i f
  · exact mixedProductAdditionSpec_z_regular W hΔ 1 2
      (.inl rfl) (.inr rfl) (.inr rfl) i f
  · exact yProductAdditionSpec_z_regular W hΔ i f

end FLT.Mazur.WeierstrassIntegralChart
