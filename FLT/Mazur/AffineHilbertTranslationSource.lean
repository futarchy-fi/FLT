/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationRelation

/-!
# Actual source restrictions induced by translation changes

The source is the pullback of the actual changed Hilbert chart. Its map to
the old source is also the pullback of the translation map. Thus a genuine
open translation refinement constructs an open source refinement, and the
new chart parameter still satisfies the required open immersion condition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "C" => baseMarkedChartChange f b d

/-- Changing translation by an open immersion gives an actual open chart comparison. -/
instance translationChartChange_isOpenImmersion [IsOpenImmersion b.left] :
    IsOpenImmersion (baseMarkedChartChange f b d).left :=
  MorphismProperty.of_isPullback
    ((baseMarkedChartChange_isPullback f b d).map (Over.forget _)).flip
    (inferInstanceAs (IsOpenImmersion b.left))

/-- The actual refined source, retaining its full original chart parameter. -/
def translationSource : Over (Spec (.of R)) := pullback k C

/-- The source comparison is the original pullback projection. -/
def translationSourceMap : translationSource f d b k ⟶ A := pullback.fst k C

/-- The parameter map into the genuinely refined translation chart. -/
def translationSourceChart : translationSource f d b k ⟶ variableHilbertTest f d W :=
  pullback.snd k C

@[reassoc]
theorem translationSource_square : translationSourceMap f d b k ≫ k =
    translationSourceChart f d b k ≫ C := pullback.condition

/-- The source refinement is exactly the base change of the translation refinement. -/
theorem translationSource_isPullback :
    IsPullback (translationSourceMap f d b k)
      (translationSourceChart f d b k ≫ variableHilbertBase f d W)
      (k ≫ variableHilbertBase f d V) b :=
  (IsPullback.of_hasPullback k C).paste_vert (baseMarkedChartChange_isPullback f b d)

/-- All base-change-stable properties of the translation comparison survive on the source. -/
theorem translationSourceMap_property (P : MorphismProperty Scheme)
    [P.IsStableUnderBaseChange] (hb : P b.left) :
    P (translationSourceMap f d b k).left :=
  MorphismProperty.of_isPullback
    ((translationSource_isPullback f d b k).map (Over.forget _)).flip hb

instance translationSourceMap_isOpenImmersion [IsOpenImmersion b.left] :
    IsOpenImmersion (translationSourceMap f d b k).left :=
  translationSourceMap_property f d b k _ inferInstance

/-- The chart parameter retains the open immersion needed by invariant denominators. -/
instance translationSourceChart_isOpenImmersion [IsOpenImmersion k.left] :
    IsOpenImmersion (translationSourceChart f d b k).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback k C).map (Over.forget _))
      (inferInstanceAs (IsOpenImmersion k.left))

/-- Affine translations give actual affine refinements of every affine source. -/
instance translationSource_affine [IsAffine A.left] [IsAffine V.left] [IsAffine W.left] :
    IsAffine (translationSource f d b k).left :=
  by
    have H := (translationSource_isPullback f d b k).map (Over.forget _)
    change IsPullback _ _ (k ≫ variableHilbertBase f d V).left b.left at H
    exact IsAffine.of_isPullback H

/-- The original Picard class is preserved on this constructed source refinement. -/
theorem translationSource_class :
    (relativeFppfSheaf f).obj.map (translationSourceMap f d b k).op
        (sectionAt f hL d V c k) =
      sectionAt f hL d W ((relativeFppfSheaf f).obj.map b.op c)
        (translationSourceChart f d b k) := by
  rw [← translation_sectionAt f hL d b c (translationSourceChart f d b k)]
  simp only [sectionAt, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← translationSource_square]

end FLT.Mazur.HilbertChart.AffineRestriction
