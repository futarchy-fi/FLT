/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullRelationRestriction
public import FLT.Mazur.RelativeRelationOrbitTopology

/-!
# Restricting the full Hilbert relation gives the exact original orbit open

The restricted orbit map is injective because every original arrow between
restricted endpoints lifts. Open source restrictions induce open embeddings
of orbit spaces, without assuming the source open is invariant or affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "e" => variableChartEquivalenceRelation f hL d V c
local notation "a" => equivalence f hL d V c k

/-- The original orbit map is constant on the full restricted relation. -/
theorem restricted_projection_pair (z : (relation f hL d V c k).left) :
    projection e (k.left ((fst f hL d V c k).left z)) =
      projection e (k.left ((snd f hL d V c k).left z)) := by
  have h := projection_pair e ((toFullRelation f hL d V c k).left z)
  have h₁ := congrArg (fun g ↦ g.left z) (toFullRelation_fst f hL d V c k)
  have h₂ := congrArg (fun g ↦ g.left z) (toFullRelation_snd f hL d V c k)
  exact h₁ ▸ h₂ ▸ h

/-- The point quotient of the full restricted relation maps to the original orbit space. -/
def restrictedOrbitMap : Orbit a → Orbit e :=
  descend a (fun x ↦ projection e (k.left x)) (restricted_projection_pair f hL d V c k)

/-- The descended map retains the original source inclusion on every point. -/
theorem restrictedOrbitMap_projection (x : A.left) :
    restrictedOrbitMap f hL d V c k (projection a x) = projection e (k.left x) := rfl

/-- No new point identifications appear after restricting the full relation. -/
theorem restrictedOrbitMap_injective : Function.Injective (restrictedOrbitMap f hL d V c k) := by
  intro z w h
  obtain ⟨x, rfl⟩ := projection_surjective a z
  obtain ⟨y, rfl⟩ := projection_surjective a w
  obtain ⟨t, ht, hs⟩ := (projection_eq_iff e _ _).mp h
  obtain ⟨b, hb, hc⟩ := original_arrow_lift f hL d V c k t x y ht hs
  exact (projection_eq_iff a x y).mpr ⟨b, hb, hc⟩

/-- The comparison uses precisely the original quotient topologies. -/
theorem restrictedOrbitMap_continuous : Continuous (restrictedOrbitMap f hL d V c k) :=
  descend_continuous a _ (restricted_projection_pair f hL d V c k)
    ((projection_continuous e).comp k.left.continuous)

/-- The comparison image consists exactly of original orbits meeting the restricted source. -/
theorem restrictedOrbitMap_range :
    Set.range (restrictedOrbitMap f hL d V c k) = projection e '' Set.range k.left := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := projection_surjective a w
    exact ⟨k.left x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨projection a x, rfl⟩

/-- An open source restriction induces an open embedding of its full orbit quotient. -/
theorem restrictedOrbitMap_isOpenEmbedding [Etale V.hom] [IsOpenImmersion k.left] :
    IsOpenEmbedding (restrictedOrbitMap f hL d V c k) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (restrictedOrbitMap_continuous f hL d V c k) (restrictedOrbitMap_injective f hL d V c k)
  apply IsOpenMap.of_comp (projection_continuous a) (projection_surjective a)
  exact (projection_isOpenMap e (variableChartRelationSnd f hL d V c).left.isOpenMap).comp
    k.left.isOpenMap

/-- The restricted quotient is homeomorphic to its exact original orbit image. -/
def restrictedOrbitHomeomorph [Etale V.hom] [IsOpenImmersion k.left] :
    Orbit a ≃ₜ (projection e '' Set.range k.left) :=
  (restrictedOrbitMap_isOpenEmbedding f hL d V c k).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (restrictedOrbitMap_range f hL d V c k))

/-- This topological identification preserves the original quotient projection. -/
theorem restrictedOrbitHomeomorph_projection [Etale V.hom] [IsOpenImmersion k.left]
    (x : A.left) :
    (restrictedOrbitHomeomorph f hL d V c k (projection a x)).val =
      projection e (k.left x) := rfl

end FLT.Mazur.HilbertChart.AffineRestriction
