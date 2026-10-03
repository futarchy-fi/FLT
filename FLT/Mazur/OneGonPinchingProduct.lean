/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonProductDescent
public import FLT.Mazur.PinchingPullbackTransport

/-!
# The one-gon pinching pushout after affine parameter base change

The singleton coproduct and pullback symmetry transport one-gon descent to
its exact specified pinching cocone over an arbitrary coefficient algebra.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.OneGonPinchingProduct
open PinchingPullbackTransport OneGonProductNormalization PinchingChartBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
/-- Identify the projective line with its singleton coproduct. -/
def componentsIso : PolygonPinching.component K ≅ PolygonPinching.components K 1 :=
  (coproductUniqueIso (fun _ : Fin 1 ↦ PolygonPinching.component K)).symm
/-- The normalization source after affine parameter base change. -/
def sourceIso : Over.mk (pullback.fst (parameter K S) (ProjectiveLine.toBase K)) ≅
    (Over.pullback (parameter K S)).obj (PolygonPinching.components K 1) :=
  comparison (parameter K S) (componentsIso K)
/-- The one-gon after reversing the pullback convention. -/
def targetIso : Over.mk (pullback.fst (parameter K S) (OneGonGluing.toBase K)) ≅
    (Over.pullback (parameter K S)).obj (OneGonNormalization.polygon K) :=
  swap (parameter K S) (OneGonNormalization.polygon K)
@[reassoc] theorem normalization_comparison :
    (sourceIso K S).hom.left ≫
      ((Over.pullback (parameter K S)).map (OneGonNormalization.normalizationOver K)).left =
    normalizationProduct K S ≫ (targetIso K S).hom.left := by
  apply pullback.hom_ext
  · simp [normalizationProduct, sourceIso, targetIso, swap, OneGonNormalization.polygon,
      Over.pullback,
      componentsIso, ← Over.comp_left, OneGonNormalization.normalizationOver,
      parameter, ProjectiveLineProductCharts.parameterToBase]
  · simp [normalizationProduct, sourceIso, targetIso, swap, OneGonNormalization.polygon,
      Over.pullback,
      parameter, ProjectiveLineProductCharts.parameterToBase]
@[reassoc] theorem endpoint_comparison (hpos : 0 < 1) (b : Bool) :
    OneGonProductEndpoints.endpoint K S b ≫ (sourceIso K S).hom.left =
      sectionMap (parameter K S) (PolygonPinching.endpoint K 1 hpos 0 b) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, sourceIso, comparison_fst,
      sectionMap, pullback.lift_fst]
    cases b <;> simp [OneGonProductEndpoints.endpoint,
      parameter, ProjectiveLineProductCharts.parameterToBase, componentsIso,
      PolygonPinching.endpoint,
      PolygonPinching.componentι,
      ProjectiveLine.zeroSection, ProjectiveLine.infinitySection]
  · simp [sourceIso, sectionMap, OneGonProductEndpoints.endpoint,
      parameter, ProjectiveLineProductCharts.parameterToBase]
theorem exists_desc (hpos : 0 < 1) {Y : Over (Spec (.of S))}
    (f : (Over.pullback (parameter K S)).obj (PolygonPinching.components K 1) ⟶ Y)
    (q : (Over.pullback (parameter K S)).obj (PolygonPinching.nodes K 1) ⟶ Y)
    (w : (Over.pullback (parameter K S)).map (PolygonPinching.toComponents K 1 hpos) ≫ f =
      (Over.pullback (parameter K S)).map (PolygonPinching.toNodes K 1) ≫ q) :
    ∃! d : (Over.pullback (parameter K S)).obj (OneGonNormalization.polygon K) ⟶ Y,
      (Over.pullback (parameter K S)).map (OneGonNormalization.normalizationOver K) ≫ d = f := by
  let h := (sourceIso K S).hom.left ≫ f.left
  have hw : OneGonProductEndpoints.endpoint K S false ≫ h =
      OneGonProductEndpoints.endpoint K S true ≫ h := by
    dsimp [h]
    rw [endpoint_comparison_assoc K S hpos, endpoint_comparison_assoc K S hpos]
    exact input_condition K 1 (parameter K S) hpos f q w 0
  obtain ⟨d, hd, hu⟩ := OneGonProductDescent.exists_desc K S h hw
  have hb : d ≫ Y.hom = pullback.fst _ _ :=
    OneGonProductDescent.desc_toBase K S h Y.hom (by
      dsimp [h]
      rw [Category.assoc, Over.w]
      exact (sourceIso K S).hom.w) d hd
  let d' : Over.mk (pullback.fst (parameter K S) (OneGonGluing.toBase K)) ⟶ Y :=
    Over.homMk d hb
  refine ⟨(targetIso K S).inv ≫ d', ?_, ?_⟩
  · apply (cancel_epi (sourceIso K S).hom).mp
    apply Over.OverMorphism.ext
    change (sourceIso K S).hom.left ≫ _ ≫ _ ≫ d = _
    rw [normalization_comparison_assoc]
    rw [← Category.assoc (targetIso K S).hom.left, ← Over.comp_left,
      Iso.hom_inv_id, Over.id_left, Category.id_comp]
    exact hd
  · intro e he
    apply (cancel_epi (targetIso K S).hom).mp
    apply Over.OverMorphism.ext
    change (targetIso K S).hom.left ≫ e.left = _
    have hh : normalizationProduct K S ≫
        ((targetIso K S).hom.left ≫ e.left) = h := by
      rw [← normalization_comparison_assoc]
      change (sourceIso K S).hom.left ≫ ( _ ≫ e).left = h
      rw [he]
    have heq := hu _ hh
    simpa only [Over.comp_left, ← Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.id_comp, d', Over.homMk_left] using heq

theorem isPushout (hpos : 0 < 1) :
    IsPushout ((Over.pullback (parameter K S)).map (PolygonPinching.toComponents K 1 hpos))
      ((Over.pullback (parameter K S)).map (PolygonPinching.toNodes K 1))
      ((Over.pullback (parameter K S)).map (OneGonNormalization.normalizationOver K))
      ((Over.pullback (parameter K S)).map (OneGonNormalization.nodes K)) := by
  apply PinchingPushoutCriterion.isPushout_of_existsUnique
  · rw [← Functor.map_comp, ← Functor.map_comp, OneGonNormalization.cocone]
  · intro Y f q w
    exact exists_desc K S hpos f q w
end FLT.Mazur.OneGonPinchingProduct
