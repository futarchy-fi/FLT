/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableTranslatedHilbertRepresentation
public import FLT.Mazur.SmoothHilbertSourcePullback

/-!
# Smooth covers of Hilbert charts over local translation bases

The variable-base intersection with the original source is its actual smooth
surjective cover. When the translation base is open in the original base, the
source intersection is open too. No extension of the translation is required.
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
  (d : ℕ) (T : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op T))

/-- The universal translated section retains the actual local base. -/
def variableChartSection :
    (relativeFppfSheaf f).obj.obj (op (variableHilbertTest f d T)) :=
  variableHilbertPoint f d hL T c _ (𝟙 _)

/-- Pulling back the universal section recovers the original variable chart formula. -/
theorem variableChartSection_map {U : Over (Spec (.of R))}
    (a : U ⟶ variableHilbertTest f d T) :
    (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d T c) =
      variableHilbertPoint f d hL T c U a := by
  rw [variableChartSection, ← variableHilbertPoint_natural, Category.comp_id]

/-- The actual intersection of the fixed source with the variable-base chart. -/
def variableSourceIntersection : Over (Spec (.of R)) :=
  variableHilbertOverlap f d T c _ (smoothHilbertSourceSection f hL)

/-- Its projection to the original source, open when the translation base is open. -/
def variableSourceInclusion : variableSourceIntersection f hL d T c ⟶ smoothHilbertSource f :=
  variableHilbertOverlapToTest f d T c _ (smoothHilbertSourceSection f hL)

instance variableSourceInclusion_isOpenImmersion [IsOpenImmersion T.hom] :
    IsOpenImmersion (variableSourceInclusion f hL d T c).left :=
  variableHilbertOverlapToTest_isOpenImmersion _ _ _ _ _ _

/-- Its actual map to the translated Hilbert parameter scheme. -/
def variableSourceParameter :
    variableSourceIntersection f hL d T c ⟶ variableHilbertTest f d T :=
  variableHilbertOverlapToChart f d hL T c _ (smoothHilbertSourceSection f hL)

/-- Both maps retain the same original Picard section. -/
theorem variableSourceIntersection_class :
    (relativeFppfSheaf f).obj.map (variableSourceInclusion f hL d T c).op
      (smoothHilbertSourceSection f hL) =
    (relativeFppfSheaf f).obj.map (variableSourceParameter f hL d T c).op
      (variableChartSection f hL d T c) := by
  rw [variableChartSection_map]
  exact (variableHilbertOverlap_class f d hL T c _ _).symm

/-- Compare the chart intersection to the full smooth source pullback. -/
def variableSourceToSmooth : variableSourceIntersection f hL d T c ⟶
    smoothHilbertIntersectionSource f hL _ (variableChartSection f hL d T c) :=
  (smoothHilbertIntersection_lift f hL _ _ _ _
    (variableSourceIntersection_class f hL d T c)).choose

@[reassoc]
theorem variableSourceToSmooth_source :
    variableSourceToSmooth f hL d T c ≫ smoothHilbertIntersectionToSource f hL _ _ =
      variableSourceInclusion f hL d T c :=
  (smoothHilbertIntersection_lift f hL _ _ _ _
    (variableSourceIntersection_class f hL d T c)).choose_spec.1.1

@[reassoc]
theorem variableSourceToSmooth_parameter :
    variableSourceToSmooth f hL d T c ≫ smoothHilbertIntersectionToTest f hL _ _ =
      variableSourceParameter f hL d T c :=
  (smoothHilbertIntersection_lift f hL _ _ _ _
    (variableSourceIntersection_class f hL d T c)).choose_spec.1.2

/-- The inverse comparison uses the original open chart's universal property. -/
def smoothToVariableSource :
    smoothHilbertIntersectionSource f hL _ (variableChartSection f hL d T c) ⟶
      variableSourceIntersection f hL d T c :=
  (variableHilbertOverlap_lift f d hL T c _ _
    (smoothHilbertIntersectionToSource f hL _ _)
    (smoothHilbertIntersectionToTest f hL _ _) (by
      rw [← variableChartSection_map]
      exact (smoothHilbertIntersectionSource_class f hL _ _).symm)).choose

@[reassoc]
theorem smoothToVariableSource_source :
    smoothToVariableSource f hL d T c ≫ variableSourceInclusion f hL d T c =
      smoothHilbertIntersectionToSource f hL _ _ :=
  (variableHilbertOverlap_lift f d hL T c _ _ _ _ (by
    rw [← variableChartSection_map]
    exact (smoothHilbertIntersectionSource_class f hL _ _).symm)).choose_spec.1.1

@[reassoc]
theorem smoothToVariableSource_parameter :
    smoothToVariableSource f hL d T c ≫ variableSourceParameter f hL d T c =
      smoothHilbertIntersectionToTest f hL _ _ :=
  (variableHilbertOverlap_lift f d hL T c _ _ _ _ (by
    rw [← variableChartSection_map]
    exact (smoothHilbertIntersectionSource_class f hL _ _).symm)).choose_spec.1.2

/-- The source intersection is the actual smooth cover of the variable-base chart. -/
def variableSourceSmoothIso : variableSourceIntersection f hL d T c ≅
    smoothHilbertIntersectionSource f hL _ (variableChartSection f hL d T c) where
  hom := variableSourceToSmooth f hL d T c
  inv := smoothToVariableSource f hL d T c
  hom_inv_id := by
    apply variableHilbertOverlap_hom_ext f d hL T c _ _
    · change _ ≫ variableSourceInclusion f hL d T c =
        _ ≫ variableSourceInclusion f hL d T c
      rw [Category.assoc, smoothToVariableSource_source,
        variableSourceToSmooth_source, Category.id_comp]
    · change _ ≫ variableSourceParameter f hL d T c =
        _ ≫ variableSourceParameter f hL d T c
      rw [Category.assoc, smoothToVariableSource_parameter,
        variableSourceToSmooth_parameter, Category.id_comp]
  inv_hom_id := by
    apply smoothHilbertIntersection_hom_ext f hL _ _
    · simp only [Category.assoc, variableSourceToSmooth_source,
        smoothToVariableSource_source, Category.id_comp]
    · simp only [Category.assoc, variableSourceToSmooth_parameter,
        smoothToVariableSource_parameter, Category.id_comp]

instance variableSourceParameter_smooth : Smooth (variableSourceParameter f hL d T c).left := by
  rw [← variableSourceToSmooth_parameter]
  change Smooth ((variableSourceSmoothIso f hL d T c).hom.left ≫ _)
  infer_instance

instance variableSourceParameter_surjective :
    Surjective (variableSourceParameter f hL d T c).left := by
  rw [← variableSourceToSmooth_parameter]
  change Surjective ((variableSourceSmoothIso f hL d T c).hom.left ≫ _)
  infer_instance

end FLT.Mazur.HilbertChart
