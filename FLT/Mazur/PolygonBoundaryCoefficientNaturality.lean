/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierBoundarySectionRingNaturality
public import FLT.Mazur.PolygonStageCoefficientBoundary
public import FLT.Mazur.PolygonSectionRingFunctor

/-!
# Coefficient naturality in all original boundary section rings

The commutative family square and the retained full Cartier ideals prove
naturality of the actual section maps for every original stage transition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] family
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (h : 2 ≤ n)

/-- The coefficient pullback commutes with every original boundary section restriction. -/
theorem coefficientBoundarySections_naturality {a b : ℕ} (g : a ⟶ b) :
    (boundarySectionsMap S n h g).comp (coefficientBoundarySections f b n h) =
      (coefficientBoundarySections f a n h).comp (boundarySectionsMap R n h g) := by
  exact cartierSectionRingMap_square
    ((stageSystem S n h).map g) (stageCoefficientFamily f b n h)
    (stageCoefficientFamily f a n h) ((stageSystem R n h).map g)
    (stageCoefficientFamily_naturality f n h g)
    (boundaryIdeal_cartier R b n h).1 (boundaryIdeal_cartier S b n h).1
    (boundaryIdeal_cartier R a n h).1 (boundaryIdeal_cartier S a n h).1
    (boundaryIdeal_stageCoefficientFamily f b n h) (boundaryIdeal_systemMap S n h g)
    (boundaryIdeal_systemMap R n h g) (boundaryIdeal_stageCoefficientFamily f a n h)

/-- The full inverse functors of boundary section rings retain coefficient pullback. -/
def coefficientBoundarySectionFunctor :
    boundarySectionRingFunctor R n h ⟶ boundarySectionRingFunctor S n h where
  app m := CommRingCat.ofHom (coefficientBoundarySections f m.unop n h)
  naturality _ _ g := by
    apply CommRingCat.hom_ext
    exact (coefficientBoundarySections_naturality f n h g.unop).symm

end FLT.Mazur.PolygonInfinitesimalStages
