/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationInvariantOpenFunctor

/-!
# Section domains on the quotient neighborhood

The open embedding into the original quotient and the chart homeomorphism
induce exactly the domains already used by the section-ring comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The original quotient neighborhood as a topological object. -/
def smoothTranslationNeighborhood : TopCat :=
  TopCat.of (smoothTranslationOrbitOpen f hL d V c)

/-- The constructed chart homeomorphism, as an isomorphism of topological objects. -/
def smoothTranslationChartTopIso :
    space (variableChartEquivalenceRelation f hL d V c) ≅
      smoothTranslationNeighborhood f hL d V c :=
  TopCat.isoOfHomeo (smoothTranslationChartOrbitHomeomorph f hL d V c)

/-- The original quotient domain corresponding to an open of the neighborhood. -/
def smoothTranslationNeighborhoodOpen
    (W : TopologicalSpace.Opens (smoothTranslationNeighborhood f hL d V c)) :
    TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  (TopologicalSpace.Opens.isOpenEmbedding
    (X := space (smoothHilbertEquivalenceRelation f hL))
    (smoothTranslationOrbitOpen f hL d V c)).functor.obj W

/-- The original domain lies in the actual quotient neighborhood. -/
theorem smoothTranslationNeighborhoodOpen_le
    (W : TopologicalSpace.Opens (smoothTranslationNeighborhood f hL d V c)) :
    smoothTranslationNeighborhoodOpen f hL d V c W ≤
      smoothTranslationOrbitOpen f hL d V c := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- Neighborhood open inclusions retain their original quotient inclusions. -/
theorem smoothTranslationNeighborhoodOpen_mono
    {W Z : TopologicalSpace.Opens (smoothTranslationNeighborhood f hL d V c)} (h : W ≤ Z) :
    smoothTranslationNeighborhoodOpen f hL d V c W ≤
      smoothTranslationNeighborhoodOpen f hL d V c Z :=
  ((TopologicalSpace.Opens.isOpenEmbedding
    (X := space (smoothHilbertEquivalenceRelation f hL))
    (smoothTranslationOrbitOpen f hL d V c)).functor.map (homOfLE h)).le

/-- Chart domains are precisely inverse images under the actual neighborhood homeomorphism. -/
theorem smoothTranslationNeighborhoodChartOpen_eq
    (W : TopologicalSpace.Opens (smoothTranslationNeighborhood f hL d V c)) :
    smoothTranslationFullChartOrbitOpen f hL d V c
        (smoothTranslationNeighborhoodOpen f hL d V c W) =
      (TopologicalSpace.Opens.map (smoothTranslationChartTopIso f hL d V c).hom).obj W := by
  rw [smoothTranslationFullChartOrbitOpen_eq_preimage]
  ext z
  change (smoothTranslationChartOrbitToOpen f hL d V c z).val ∈
      Subtype.val '' (W : Set (smoothTranslationNeighborhood f hL d V c)) ↔
    smoothTranslationChartOrbitToOpen f hL d V c z ∈ W
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = smoothTranslationChartOrbitToOpen f hL d V c z) ▸ hw
  · intro hz
    exact ⟨_, hz, rfl⟩

end FLT.Mazur.HilbertChart
