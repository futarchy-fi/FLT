/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationSectionNaturality
public import FLT.Mazur.SmoothTranslationNeighborhoodDomains

/-!
# The actual invariant sheaves agree over a translation neighborhood

Naturality packages the original section equivalences into an isomorphism of
sheaves across the already constructed homeomorphism of orbit spaces.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The actual original invariant ringed space restricted to its translation neighborhood. -/
def smoothTranslationOriginalRingedNeighborhood : SheafedSpace CommRingCat :=
  (ringedSpace (smoothHilbertEquivalenceRelation f hL)).restrict
    (TopologicalSpace.Opens.isOpenEmbedding
      (X := space (smoothHilbertEquivalenceRelation f hL))
      (smoothTranslationOrbitOpen f hL d V c))

/-- The actual chart invariant sheaf transported to the original quotient neighborhood. -/
def smoothTranslationChartNeighborhoodSheaf :
    (smoothTranslationNeighborhood f hL d V c).Sheaf CommRingCat :=
  (TopCat.Sheaf.pushforward _ (smoothTranslationChartTopIso f hL d V c).hom).obj
    (invariantSheaf (variableChartEquivalenceRelation f hL d V c))

/-- Section comparison on the actual neighborhood domain, including its final transport. -/
def smoothTranslationNeighborhoodSectionIso
    (W : TopologicalSpace.Opens (smoothTranslationNeighborhood f hL d V c)) :
    (smoothTranslationOriginalRingedNeighborhood f hL d V c).presheaf.obj (op W) ≅
      (smoothTranslationChartNeighborhoodSheaf f hL d V c).obj.obj (op W) :=
  (smoothTranslationInvariantSectionRingEquiv f hL d V c
    (smoothTranslationNeighborhoodOpen f hL d V c W)
    (smoothTranslationNeighborhoodOpen_le f hL d V c W)).toCommRingCatIso ≪≫
      (invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.mapIso
        (eqToIso (congrArg op (smoothTranslationNeighborhoodChartOpen_eq f hL d V c W)))

/-- The section isomorphisms commute with every neighborhood restriction. -/
theorem smoothTranslationNeighborhoodSectionIso_natural
    {W Z : TopologicalSpace.Opens (smoothTranslationNeighborhood f hL d V c)} (h : W ≤ Z) :
    (smoothTranslationOriginalRingedNeighborhood f hL d V c).presheaf.map (homOfLE h).op ≫
        (smoothTranslationNeighborhoodSectionIso f hL d V c W).hom =
      (smoothTranslationNeighborhoodSectionIso f hL d V c Z).hom ≫
        (smoothTranslationChartNeighborhoodSheaf f hL d V c).obj.map (homOfLE h).op := by
  ext s
  have hn := smoothTranslationInvariantSectionRingEquiv_natural f hL d V c
    (smoothTranslationNeighborhoodOpen_mono f hL d V c h)
    (smoothTranslationNeighborhoodOpen_le f hL d V c Z) s
  exact (congrArg
    ((invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.map
      (eqToHom (congrArg op (smoothTranslationNeighborhoodChartOpen_eq f hL d V c W))))
    hn).trans (sectionTransport_naturality _
      (smoothTranslationNeighborhoodChartOpen_eq f hL d V c Z)
      (smoothTranslationNeighborhoodChartOpen_eq f hL d V c W) _ _ _)

/-- The actual restricted original and transported chart presheaves are isomorphic. -/
def smoothTranslationInvariantPresheafIso :
    (smoothTranslationOriginalRingedNeighborhood f hL d V c).presheaf ≅
      (smoothTranslationChartNeighborhoodSheaf f hL d V c).obj :=
  NatIso.ofComponents (fun W ↦ smoothTranslationNeighborhoodSectionIso f hL d V c W.unop)
    (fun i ↦ smoothTranslationNeighborhoodSectionIso_natural f hL d V c i.unop.le)

/-- The comparison is an isomorphism of the actual invariant sheaves. -/
def smoothTranslationInvariantSheafIso :
    (smoothTranslationOriginalRingedNeighborhood f hL d V c).sheaf ≅
      smoothTranslationChartNeighborhoodSheaf f hL d V c where
  hom := ⟨(smoothTranslationInvariantPresheafIso f hL d V c).hom⟩
  inv := ⟨(smoothTranslationInvariantPresheafIso f hL d V c).inv⟩
  hom_inv_id := by
    exact Sheaf.hom_ext (smoothTranslationInvariantPresheafIso f hL d V c).hom_inv_id
  inv_hom_id := by
    exact Sheaf.hom_ext (smoothTranslationInvariantPresheafIso f hL d V c).inv_hom_id

end FLT.Mazur.HilbertChart
