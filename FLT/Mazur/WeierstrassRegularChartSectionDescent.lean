/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartFactorUnit
public import FLT.Mazur.WeierstrassTransportedOutputRegular

/-!
# Regular chart coordinates under covers and chart changes

Regularity of a section descends through an actual open cover. For a point
with a Y/Z presentation it is also preserved by changing the output chart
between Y and Z. Neither operation requires flatness of the point morphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Source composition is pullback of the specialized chart sections. -/
theorem specSectionHom_precomp {X Y : Scheme.{u}} {A : Type u} [CommRing A]
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of A)) :
    specSectionHom (f ≫ g) = f.appTop.hom.comp (specSectionHom g) := by
  unfold specSectionHom
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- Regularity of a global section can be checked on any actual open cover. -/
theorem isRegular_of_openCover {X : Scheme.{u}} (C : X.OpenCover) (a : Γ(X, ⊤))
    (ha : ∀ i, IsRegular ((C.f i).appTop a)) : IsRegular a := by
  have hl : IsLeftRegular a := by
    intro b c h
    apply C.ext_elem b c
    intro i
    have he := (ha i).left (by simpa only [map_mul] using congrArg (C.f i).appTop h)
    exact he
  exact ⟨hl, fun b c h => hl (by simpa only [mul_comm] using h)⟩

/-- Regularity of a specialized coordinate can be checked on an open cover of its source. -/
theorem specSectionHom_isRegular_of_cover {X : Scheme.{u}} {A : Type u} [CommRing A]
    (C : X.OpenCover) (f : X ⟶ Spec (.of A)) (a : A)
    (ha : ∀ i, IsRegular (specSectionHom (C.f i ≫ f) a)) :
    IsRegular (specSectionHom f a) := by
  apply isRegular_of_openCover C
  intro i
  simpa only [specSectionHom_precomp, RingHom.comp_apply] using ha i

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A regular normalized Z coordinate transfers between actual Y/Z chart presentations. -/
theorem chart_z_regular_of_global_eq {X : Scheme.{u}} (b : Bool) (j : Fin 3)
    (hj : j = 1 ∨ j = 2) (f : X ⟶ chartScheme W (productChartCoordinate b))
    (g : X ⟶ chartScheme W j)
    (h : f ≫ integralCurveChart W (productChartCoordinate b) = g ≫ integralCurveChart W j)
    (hz : IsRegular (specSectionHom g (coord W j 2))) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) := by
  cases b with
  | false => exact affineOutput_z_regular W f
  | true =>
    rcases hj with rfl | rfl
    · have he : f = g := (cancel_mono (integralCurveChart W 1)).mp h
      exact he ▸ hz
    · exact (chartCoordinate_isUnit_of_global_eq W 1 2 f g h).isRegular

end FLT.Mazur.WeierstrassIntegralChart
