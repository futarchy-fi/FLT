/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertSourceRepresentable

/-!
# The actual relation scheme of the smooth Picard presentation

The self-intersection represents equality of original Picard classes. Its two
projections are jointly monic, and every equal-class pair has a unique lift.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- The actual scheme of equal-class pairs in the assembled source. -/
def smoothHilbertRelation : Over (Spec (.of R)) :=
  smoothHilbertIntersectionSource f hB (smoothHilbertSource f) (smoothHilbertSourceSection f hB)

/-- The first source projection of the relation. -/
def smoothHilbertRelationFst : smoothHilbertRelation f hB ⟶ smoothHilbertSource f :=
  smoothHilbertIntersectionToSource f hB (smoothHilbertSource f)
    (smoothHilbertSourceSection f hB)

/-- The second source projection of the relation. -/
def smoothHilbertRelationSnd : smoothHilbertRelation f hB ⟶ smoothHilbertSource f :=
  smoothHilbertIntersectionToTest f hB (smoothHilbertSource f)
    (smoothHilbertSourceSection f hB)

/-- The represented relation is the full kernel pair in original presheaves. -/
theorem smoothHilbertRelation_isPullback :
    IsPullback (uliftYoneda.{1}.map (smoothHilbertRelationFst f hB))
      (uliftYoneda.{1}.map (smoothHilbertRelationSnd f hB))
      (smoothHilbertSourceMap f hB) (smoothHilbertSourceMap f hB) :=
  smoothHilbertSourceMap_isPullback f hB _ _

/-- The two original classes agree on the actual relation scheme. -/
theorem smoothHilbertRelation_class :
    (relativeFppfSheaf f).obj.map (smoothHilbertRelationFst f hB).op
      (smoothHilbertSourceSection f hB) =
        (relativeFppfSheaf f).obj.map (smoothHilbertRelationSnd f hB).op
          (smoothHilbertSourceSection f hB) :=
  smoothHilbertIntersectionSource_class f hB _ _

/-- Joint monicity holds on every original test. -/
theorem smoothHilbertRelation_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ smoothHilbertRelation f hB}
    (h₁ : a ≫ smoothHilbertRelationFst f hB = b ≫ smoothHilbertRelationFst f hB)
    (h₂ : a ≫ smoothHilbertRelationSnd f hB = b ≫ smoothHilbertRelationSnd f hB) : a = b :=
  smoothHilbertIntersection_hom_ext f hB _ _ h₁ h₂

/-- Exactly equal original classes have a unique morphism into the actual relation. -/
theorem smoothHilbertRelation_lift {T : Over (Spec (.of R))}
    (a b : T ⟶ smoothHilbertSource f)
    (h : (relativeFppfSheaf f).obj.map a.op (smoothHilbertSourceSection f hB) =
      (relativeFppfSheaf f).obj.map b.op (smoothHilbertSourceSection f hB)) :
    ∃! q : T ⟶ smoothHilbertRelation f hB,
      q ≫ smoothHilbertRelationFst f hB = a ∧ q ≫ smoothHilbertRelationSnd f hB = b :=
  smoothHilbertIntersection_lift f hB _ _ a b h

/-- The second relation projection is a smooth surjection. -/
instance smoothHilbertRelationSnd_smooth : Smooth (smoothHilbertRelationSnd f hB).left :=
  smoothHilbertIntersectionToTest_smooth f hB _ _

/-- The second relation projection covers every source point. -/
instance smoothHilbertRelationSnd_surjective : Surjective (smoothHilbertRelationSnd f hB).left :=
  smoothHilbertIntersectionToTest_surjective f hB _ _

/-- The first relation projection is smooth as well. -/
instance smoothHilbertRelationFst_smooth : Smooth (smoothHilbertRelationFst f hB).left :=
  (smoothHilbertSourceMap_pullback_smooth_surjective f hB _ _ _
    (smoothHilbertRelation_isPullback f hB).flip).1

/-- The first relation projection also covers every source point. -/
instance smoothHilbertRelationFst_surjective : Surjective (smoothHilbertRelationFst f hB).left :=
  (smoothHilbertSourceMap_pullback_smooth_surjective f hB _ _ _
    (smoothHilbertRelation_isPullback f hB).flip).2

end FLT.Mazur.HilbertChart
