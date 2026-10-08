/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionLocalCharts

/-!
# Regular chart presentations of the original addition inputs

Each actual addition domain retains its original tensor-chart inputs. The
projections to either curve factor are flat, so their chart Z coordinates
stay regular on any flat restriction of an addition domain.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Either of the two original product inputs. -/
def integralCurveProductProjection (b : Bool) : integralCurveProduct W ⟶ integralCurve W :=
  if b then pullback.snd _ _ else pullback.fst _ _

/-- Both original product projections are flat over an arbitrary coefficient ring. -/
instance integralCurveProductProjection_flat (b : Bool) :
    Flat (integralCurveProductProjection W b) := by
  cases b <;> dsimp [integralCurveProductProjection] <;> infer_instance

/-- The original input chart selected by the actual addition-cover member. -/
def integralCurveAdditionInputChart (i : (integralCurveAdditionCover W hΔ).I₀)
    (b : Bool) : Bool := if b then i.1.2 else i.1.1

/-- The original tensor projection, restricted to its addition domain. -/
def integralCurveAdditionInputSpec (i : (integralCurveAdditionCover W hΔ).I₀)
    (b : Bool) : (integralCurveAdditionCover W hΔ).X i ⟶
      chartScheme W (productChartCoordinate (integralCurveAdditionInputChart W hΔ i b)) := by
  cases b
  · exact (integralInputAdditionCover W hΔ i.1.1 i.1.2).f i.2 ≫
      Spec.map (CommRingCat.ofHom (chartProductLeft W
        (productChartCoordinate i.1.1) (productChartCoordinate i.1.2)).toRingHom)
  · exact (integralInputAdditionCover W hΔ i.1.1 i.1.2).f i.2 ≫
      Spec.map (CommRingCat.ofHom (chartProductRight W
        (productChartCoordinate i.1.1) (productChartCoordinate i.1.2)).toRingHom)

/-- The exposed chart maps represent the actual original inputs in the global product. -/
theorem integralCurveAdditionInputSpec_global (i : (integralCurveAdditionCover W hΔ).I₀)
    (b : Bool) : integralCurveAdditionInputSpec W hΔ i b ≫
        integralCurveChart W
          (productChartCoordinate (integralCurveAdditionInputChart W hΔ i b)) =
      (integralCurveAdditionCover W hΔ).f i ≫ integralCurveProductProjection W b := by
  cases b
  · change (_ ≫ _) ≫ _ =
      (_ ≫ integralCurveProductChart W i.1.1 i.1.2) ≫ pullback.fst _ _
    rw [Category.assoc, Category.assoc, integralCurveProductChart_fst]
    rfl
  · change (_ ≫ _) ≫ _ =
      (_ ≫ integralCurveProductChart W i.1.1 i.1.2) ≫ pullback.snd _ _
    rw [Category.assoc, Category.assoc, integralCurveProductChart_snd]
    rfl

/-- A flat global input has a regular Z coordinate in either Y/Z chart. -/
theorem chart_z_regular_of_flat_global {X : Scheme.{u}} (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    [Flat (f ≫ integralCurveChart W (productChartCoordinate b))] :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) := by
  let _ : Flat f := MorphismProperty.of_postcomp @Flat f
    (integralCurveChart W (productChartCoordinate b))
    (inferInstance : IsOpenImmersion (integralCurveChart W (productChartCoordinate b)))
    inferInstance
  cases b
  · exact affineOutput_z_regular W f
  · exact specSectionHom_isRegular f (infinityChart_coord_z_regular W)

/-- Both original input coordinates are regular on any flat addition-domain restriction. -/
theorem integralCurveAdditionInputSpec_z_regular
    (i : (integralCurveAdditionCover W hΔ).I₀) (b : Bool)
    {X : Scheme.{u}} (f : X ⟶ (integralCurveAdditionCover W hΔ).X i) [Flat f] :
    IsRegular (specSectionHom (f ≫ integralCurveAdditionInputSpec W hΔ i b)
      (coord W (productChartCoordinate (integralCurveAdditionInputChart W hΔ i b)) 2)) := by
  have hf : Flat ((f ≫ integralCurveAdditionInputSpec W hΔ i b) ≫
      integralCurveChart W
        (productChartCoordinate (integralCurveAdditionInputChart W hΔ i b))) := by
    rw [Category.assoc, integralCurveAdditionInputSpec_global]
    infer_instance
  exact chart_z_regular_of_flat_global W _ _

end FLT.Mazur.WeierstrassIntegralChart
