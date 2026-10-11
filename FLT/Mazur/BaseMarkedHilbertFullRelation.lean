/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullGeometry
public import FLT.Mazur.BaseMarkedHilbertFullChartPullback

/-!
# The actual full equal-class relation on the glued scheme

The self-intersection is the original Picard map's full kernel pair, including
endpoints with different translation-base maps. Its smooth second projection
comes from the constructed open subscheme, not from an assumed quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)

/-- The actual scheme of all equal-original-class pairs on the glued scheme. -/
def baseMarkedFullRelation : Over (Spec (.of R)) :=
  baseMarkedFullIntersection f V a (baseMarkedGluedTest f hL V a)
    (baseMarkedGluedPicard f hL V a)

/-- The first independent glued endpoint. -/
def baseMarkedFullRelationFst : baseMarkedFullRelation f hL V a ⟶
    baseMarkedGluedTest f hL V a := baseMarkedFullToGlued f hL V a _ _

/-- The second independent glued endpoint. -/
def baseMarkedFullRelationSnd : baseMarkedFullRelation f hL V a ⟶
    baseMarkedGluedTest f hL V a := baseMarkedFullToTest f V a _ _

/-- The constructed relation is exactly the original Picard map's presheaf kernel pair. -/
theorem baseMarkedFullRelation_isPullback :
    IsPullback (uliftYoneda.{1}.map (baseMarkedFullRelationFst f hL V a))
      (uliftYoneda.{1}.map (baseMarkedFullRelationSnd f hL V a))
      (baseMarkedGluedPicardMap f hL V a) (baseMarkedGluedPicardMap f hL V a) :=
  baseMarkedGluedPicardMap_full_isPullback f hL V a _ _

/-- The two original Picard classes of the relation agree. -/
theorem baseMarkedFullRelation_class :
    baseMarkedGluedPoint f hL V a _ (baseMarkedFullRelationFst f hL V a) =
      baseMarkedGluedPoint f hL V a _ (baseMarkedFullRelationSnd f hL V a) :=
  baseMarkedFullToGlued_class f hL V a _ _

/-- Two endpoints determine a map to the actual full relation. -/
theorem baseMarkedFullRelation_hom_ext {W : Over (Spec (.of R))}
    {p q : W ⟶ baseMarkedFullRelation f hL V a}
    (h₁ : p ≫ baseMarkedFullRelationFst f hL V a = q ≫ baseMarkedFullRelationFst f hL V a)
    (h₂ : p ≫ baseMarkedFullRelationSnd f hL V a = q ≫ baseMarkedFullRelationSnd f hL V a) :
    p = q := baseMarkedFull_hom_ext f hL V a _ _ h₂ h₁

/-- Every pair with the same original Picard class has a unique full relation arrow. -/
theorem baseMarkedFullRelation_lift {W : Over (Spec (.of R))}
    (p q : W ⟶ baseMarkedGluedTest f hL V a)
    (h : baseMarkedGluedPoint f hL V a W p = baseMarkedGluedPoint f hL V a W q) :
    ∃! l : W ⟶ baseMarkedFullRelation f hL V a,
      l ≫ baseMarkedFullRelationFst f hL V a = p ∧
        l ≫ baseMarkedFullRelationSnd f hL V a = q := by
  obtain ⟨l, hl, _⟩ := baseMarkedFull_lift f hL V a _ _ q p h
  exact ⟨l, hl.symm, fun r hr ↦ baseMarkedFullRelation_hom_ext f hL V a
    (hr.1.trans hl.2.symm) (hr.2.trans hl.1.symm)⟩

instance baseMarkedFullRelationSnd_smooth [Smooth V.hom] :
    Smooth (baseMarkedFullRelationSnd f hL V a).left :=
  baseMarkedFullToTest_smooth f V a _ _

instance baseMarkedFullRelationSnd_etale [Etale V.hom] :
    Etale (baseMarkedFullRelationSnd f hL V a).left :=
  baseMarkedFullToTest_etale f V a _ _

end FLT.Mazur.HilbertChart
