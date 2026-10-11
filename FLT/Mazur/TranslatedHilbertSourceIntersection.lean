/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertChartOverlap
public import FLT.Mazur.SmoothHilbertSourcePullback

/-!
# Smooth covers of the actual translated Hilbert charts

The open intersection of a translated chart with the fixed Hilbert source
is identified with the already constructed smooth source pullback. Thus its
map to the chart is smooth and surjective, without assuming chart coverage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- The actual open part of the fixed source lying in the translated chart. -/
def translatedSourceIntersection : Over (Spec (.of R)) :=
  translatedHilbertOverlapTest f i.1 i.2 _ (smoothHilbertSourceSection f hL)

/-- Its open immersion into the original smooth source. -/
def translatedSourceInclusion : translatedSourceIntersection f hL i ⟶ smoothHilbertSource f :=
  translatedHilbertOverlapArrow f i.1 i.2 _ (smoothHilbertSourceSection f hL)

instance translatedSourceInclusion_isOpenImmersion :
    IsOpenImmersion (translatedSourceInclusion f hL i).left :=
  translatedHilbertOverlapArrow_isOpenImmersion _ _ _ _ _

/-- Its actual map to the translated Hilbert parameter scheme. -/
def translatedSourceParameter :
    translatedSourceIntersection f hL i ⟶ acyclicHilbertTest f i.1 :=
  translatedHilbertOverlapToParameter f i.1 hL i.2 _ (smoothHilbertSourceSection f hL)

/-- Both maps retain the same original Picard section. -/
theorem translatedSourceIntersection_class :
    (relativeFppfSheaf f).obj.map (translatedSourceInclusion f hL i).op
      (smoothHilbertSourceSection f hL) =
    (relativeFppfSheaf f).obj.map (translatedSourceParameter f hL i).op
      (translatedHilbertChartSection f hL i) := by
  rw [translatedHilbertChartSection_map]
  exact (translatedHilbertOverlap_class f i.1 hL i.2 _ _).symm

/-- Compare the chart intersection to the full smooth source pullback. -/
def translatedSourceToSmooth : translatedSourceIntersection f hL i ⟶
    smoothHilbertIntersectionSource f hL _ (translatedHilbertChartSection f hL i) :=
  (smoothHilbertIntersection_lift f hL _ _ _ _
    (translatedSourceIntersection_class f hL i)).choose

@[reassoc]
theorem translatedSourceToSmooth_source :
    translatedSourceToSmooth f hL i ≫ smoothHilbertIntersectionToSource f hL _ _ =
      translatedSourceInclusion f hL i :=
  (smoothHilbertIntersection_lift f hL _ _ _ _
    (translatedSourceIntersection_class f hL i)).choose_spec.1.1

@[reassoc]
theorem translatedSourceToSmooth_parameter :
    translatedSourceToSmooth f hL i ≫ smoothHilbertIntersectionToTest f hL _ _ =
      translatedSourceParameter f hL i :=
  (smoothHilbertIntersection_lift f hL _ _ _ _
    (translatedSourceIntersection_class f hL i)).choose_spec.1.2

/-- The inverse comparison uses the original open chart's universal property. -/
def smoothToTranslatedSource :
    smoothHilbertIntersectionSource f hL _ (translatedHilbertChartSection f hL i) ⟶
      translatedSourceIntersection f hL i :=
  (translatedHilbertOverlap_lift f i.1 hL i.2 _ _
    (smoothHilbertIntersectionToSource f hL _ _)
    (smoothHilbertIntersectionToTest f hL _ _) (by
      rw [← translatedHilbertChartSection_map]
      exact (smoothHilbertIntersectionSource_class f hL _ _).symm)).choose

@[reassoc]
theorem smoothToTranslatedSource_source :
    smoothToTranslatedSource f hL i ≫ translatedSourceInclusion f hL i =
      smoothHilbertIntersectionToSource f hL _ _ :=
  (translatedHilbertOverlap_lift f i.1 hL i.2 _ _ _ _ (by
    rw [← translatedHilbertChartSection_map]
    exact (smoothHilbertIntersectionSource_class f hL _ _).symm)).choose_spec.1.1

@[reassoc]
theorem smoothToTranslatedSource_parameter :
    smoothToTranslatedSource f hL i ≫ translatedSourceParameter f hL i =
      smoothHilbertIntersectionToTest f hL _ _ :=
  (translatedHilbertOverlap_lift f i.1 hL i.2 _ _ _ _ (by
    rw [← translatedHilbertChartSection_map]
    exact (smoothHilbertIntersectionSource_class f hL _ _).symm)).choose_spec.1.2

/-- The open source intersection is the actual smooth cover of the translated chart. -/
def translatedSourceSmoothIso : translatedSourceIntersection f hL i ≅
    smoothHilbertIntersectionSource f hL _ (translatedHilbertChartSection f hL i) where
  hom := translatedSourceToSmooth f hL i
  inv := smoothToTranslatedSource f hL i
  hom_inv_id := by
    let _ : Mono (translatedSourceInclusion f hL i) := Over.mono_of_mono_left _
    apply (cancel_mono (translatedSourceInclusion f hL i)).mp
    rw [Category.assoc, smoothToTranslatedSource_source,
      translatedSourceToSmooth_source, Category.id_comp]
  inv_hom_id := by
    apply smoothHilbertIntersection_hom_ext f hL _ _
    · simp only [Category.assoc, translatedSourceToSmooth_source,
        smoothToTranslatedSource_source, Category.id_comp]
    · simp only [Category.assoc, translatedSourceToSmooth_parameter,
        smoothToTranslatedSource_parameter, Category.id_comp]

instance translatedSourceParameter_smooth : Smooth (translatedSourceParameter f hL i).left := by
  rw [← translatedSourceToSmooth_parameter]
  change Smooth ((translatedSourceSmoothIso f hL i).hom.left ≫ _)
  infer_instance

instance translatedSourceParameter_surjective :
    Surjective (translatedSourceParameter f hL i).left := by
  rw [← translatedSourceToSmooth_parameter]
  change Surjective ((translatedSourceSmoothIso f hL i).hom.left ≫ _)
  infer_instance

end FLT.Mazur.HilbertChart
