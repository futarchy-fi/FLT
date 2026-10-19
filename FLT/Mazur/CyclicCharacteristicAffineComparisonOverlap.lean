/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineComparisonPullback
public import FLT.Mazur.WeierstrassComparisonCoefficientProjection

/-!
# Comparison overlap maps with named affine chart refinements

The actual pullback scheme identification permits separately named refined
chart maps. This retains the equality transports needed on multiple overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] comparisonPresentationBaseChangeIso comparisonPresentationHom
variable (n : ℕ) [NeZero n] {A B : Type} [CommRing A] [CommRing B]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
  (q' : Spec (.of B) ⟶ normalizedLocus n b) (r' : Spec (.of B) ⟶ normalizedLocus n c)
  (f : A →+* B) (hq : q' = Spec.map (CommRingCat.ofHom f) ≫ q)
  (hr : r' = Spec.map (CommRingCat.ofHom f) ≫ r)

include hq in
/-- Named affine refinements retain the actual coefficient equation equality. -/
theorem affineEquation_named_refine :
    affineEquation n b q' = (affineEquation n b q).map f :=
  (congrArg (affineEquation n b) hq).trans (affineEquation_pullback n b q f)

/-- The actual full comparison pullback on a named affine overlap. -/
def affineComparisonOverlapIso : affineComparisonScheme n b c q' r' ≅
    pullback (Spec.map (CommRingCat.ofHom f)) (affineComparisonStructure n b c q r) :=
  comparisonPresentationBaseChangeIso (affineEquation n b q) (affineEquation n c r)
    (affineEquation n b q') (affineEquation n c r') f
    (affineEquation_named_refine n b q q' f hq) (affineEquation_named_refine n c r r' f hr)

/-- The named overlap identifies the original refined coefficient-base projection. -/
@[reassoc] theorem affineComparisonOverlapIso_fst :
    (affineComparisonOverlapIso n b c q r q' r' f hq hr).hom ≫ pullback.fst _ _ =
      affineComparisonStructure n b c q' r' :=
  comparisonPresentationBaseChangeIso_structure _ _ _ _ _ _ _

/-- The named overlap gives an actual map between the full comparison schemes. -/
def affineComparisonOverlapMap : affineComparisonScheme n b c q' r' ⟶
    affineComparisonScheme n b c q r :=
  (affineComparisonOverlapIso n b c q r q' r' f hq hr).hom ≫ pullback.snd _ _

/-- The overlap map retains every universal comparison coordinate. -/
theorem affineComparisonOverlapMap_eq_spec :
    affineComparisonOverlapMap n b c q r q' r' f hq hr =
      Spec.map (CommRingCat.ofHom (comparisonPresentationHom
        (affineEquation n b q) (affineEquation n c r)
        (affineEquation n b q') (affineEquation n c r') f
        (affineEquation_named_refine n b q q' f hq)
        (affineEquation_named_refine n c r r' f hr))) :=
  comparisonPresentationBaseChangeIso_snd _ _ _ _ _ _ _

/-- The concrete refinement is the named overlap with its original composite chart maps. -/
theorem affineComparisonOverlapMap_refinement :
    affineComparisonOverlapMap n b c q r
      (Spec.map (CommRingCat.ofHom f) ≫ q) (Spec.map (CommRingCat.ofHom f) ≫ r) f rfl rfl =
        affineComparisonRefinement n b c q r f := rfl

/-- The full overlap map commutes with the prescribed coefficient-base map. -/
@[reassoc] theorem affineComparisonOverlapMap_structure :
    affineComparisonOverlapMap n b c q r q' r' f hq hr ≫
      affineComparisonStructure n b c q r =
    affineComparisonStructure n b c q' r' ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [affineComparisonOverlapMap, Category.assoc, ← pullback.condition,
    ← Category.assoc, affineComparisonOverlapIso_fst]

end FLT.Mazur.CyclicCharacteristicAtlas
