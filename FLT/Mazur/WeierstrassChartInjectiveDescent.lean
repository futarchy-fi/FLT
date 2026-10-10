/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartCrossComparison

/-!
# Injective descent for different output charts

An injective map on global sections reflects equality of chart-presented points
of the integral cubic. No common chart, reducedness, or unit descent is needed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Pulling back a chart presentation acts by the map on global sections. -/
theorem specSectionHom_precomp {X Y : Scheme.{u}} {A : Type u} [CommRing A]
    (f : Y ⟶ X) (g : X ⟶ Spec (.of A)) :
    specSectionHom (f ≫ g) = f.appTop.hom.comp (specSectionHom g) := by
  unfold specSectionHom
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  rfl

/-- Equality of points in arbitrary charts descends along an injection on sections. -/
theorem chart_global_eq_of_section_injective {X Y : Scheme.{u}}
    (f : Y ⟶ X) (hf : Function.Injective f.appTop.hom) (j k : Fin 3)
    (l : X ⟶ chartScheme W j) (r : X ⟶ chartScheme W k)
    (h : f ≫ l ≫ integralCurveChart W j = f ≫ r ≫ integralCurveChart W k) :
    l ≫ integralCurveChart W j = r ≫ integralCurveChart W k := by
  apply global_eq_of_chart_cross W j k l r
  · apply specSectionHom_injective
    apply RingHom.ext
    intro x
    apply hf
    have hb := congrArg (fun g => g ≫ integralCurveStructure W) h
    simp only [Category.assoc, integralCurveChart_structure] at hb
    have hs := congrArg specSectionHom hb
    rw [specSectionHom_precomp, specSectionHom_precomp] at hs
    exact DFunLike.congr_fun hs x
  · intro i
    apply hf
    have hc := chart_cross_of_global_eq W j k (f ≫ l) (f ≫ r)
      (by simpa only [Category.assoc] using h) i
    simpa only [specSectionHom_precomp, RingHom.comp_apply, map_mul] using hc

/-- An injective ring map induces an injection on global sections of spectra. -/
theorem specMap_appTop_injective {S T : Type u} [CommRing S] [CommRing T]
    (a : S →+* T) (ha : Function.Injective a) :
    Function.Injective (Spec.map (CommRingCat.ofHom a)).appTop.hom := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of S)).hom).injective
  apply ha
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom a)
  have hx := ConcreteCategory.congr_hom hn x
  have hy := ConcreteCategory.congr_hom hn y
  exact hx.symm.trans ((congrArg (Scheme.ΓSpecIso (.of T)).hom h).trans hy)

/-- Injective coefficient extension reflects equality of differently normalized outputs. -/
theorem chart_global_eq_of_ring_injective {S T : Type u} [CommRing S] [CommRing T]
    (a : S →+* T) (ha : Function.Injective a) (j k : Fin 3)
    (l : Spec (.of S) ⟶ chartScheme W j) (r : Spec (.of S) ⟶ chartScheme W k)
    (h : Spec.map (CommRingCat.ofHom a) ≫ l ≫ integralCurveChart W j =
      Spec.map (CommRingCat.ofHom a) ≫ r ≫ integralCurveChart W k) :
    l ≫ integralCurveChart W j = r ≫ integralCurveChart W k :=
  chart_global_eq_of_section_injective W _ (specMap_appTop_injective a ha) j k l r h

end FLT.Mazur.WeierstrassIntegralChart
