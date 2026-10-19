/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertGenericCompleteNeighborhood
public import FLT.Mazur.HilbertCompleteInteriorOriginalNeighborhoods
public import FLT.Mazur.HilbertFiniteRelationUniformCoverage

/-!
# Actual original boundary lifting near an integral generic orbit

The constructed finite neighborhood gives a surjective original boundary
restriction near the original generic orbit. The existing uniform lifting
open is consequently dense in every nonempty original orbit domain.
This does not claim coverage at boundary points outside that dense open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsIntegral A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source originalClosedInvariantMap
local notation "η" => projection eo (genericPoint A.left)

omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- The image of the original integral generic parameter is generic in the original orbit space. -/
theorem originalGenericOrbit_isGenericPoint : IsGenericPoint η Set.univ := by
  have h := (genericPoint_spec A.left).image (projection_continuous eo)
  simpa only [Set.image_univ, Set.range_eq_univ.mpr (projection_surjective eo),
    closure_univ] using h

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))

omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- Every nonempty original orbit domain contains the original generic orbit. -/
theorem originalGenericOrbit_mem (hW : (W : Set (Orbit eo)).Nonempty) : η ∈ W := by
  apply ((originalGenericOrbit_isGenericPoint f hL d V c k).mem_open_set_iff W.isOpen).mpr
  simpa only [Set.univ_inter] using hW

/-- There is an actual original neighborhood on which all original boundary sections lift. -/
theorem exists_generic_original_lifting_neighborhood (hW : (W : Set (Orbit eo)).Nonempty) :
    ∃ O : TopologicalSpace.Opens (Orbit eo),
      O ≤ W ∧ η ∈ O ∧ Function.Surjective ((m).c.app (op O)) := by
  obtain ⟨n, o, y, hy, hc⟩ := exists_complete_interior_lift_of_finiteTarget e
    (genericPoint A.left) (originalProjection_generic_finite f hL d V c k)
  have hw : normalizedFullRelationFirst f hL d V c k n o y ∈ (pullOpen eo W).val := by
    change first p q (Fin n) o y ∈ (pullOpen eo W).val
    rw [hy]
    exact originalGenericOrbit_mem f hL d V c k W hW
  obtain ⟨O, hOW, hyO, hs⟩ :=
    exists_completeInterior_original_lifting_neighborhood f hL d V c k W n o y hw hc
  refine ⟨O, hOW, ?_, hs⟩
  change projection eo (first p q (Fin n) o y) ∈ O at hyO
  rwa [hy] at hyO

/-- The constructed uniform boundary lifting domain contains the actual generic orbit. -/
theorem originalGenericOrbit_mem_uniformLiftingOpen (hW : (W : Set (Orbit eo)).Nonempty) :
    η ∈ OrbitBoundaryAtlas.uniformLiftingOpen f hL d V c k W :=
  OrbitBoundaryAtlas.projection_mem_uniformLiftingOpen_of_finiteTarget
    f hL d V c k W (genericPoint A.left) (originalGenericOrbit_mem f hL d V c k W hW)
    (originalProjection_generic_finite f hL d V c k)

/-- Uniform original lifting is dense on each nonempty domain of an integral original source. -/
theorem uniformLiftingOpen_dense_of_integral (hW : (W : Set (Orbit eo)).Nonempty) :
    Dense (OrbitBoundaryAtlas.uniformLiftingOpen f hL d V c k W : Set (Orbit eo)) := by
  have hg := originalGenericOrbit_isGenericPoint f hL d V c k
  have hs : {η} ⊆ (OrbitBoundaryAtlas.uniformLiftingOpen f hL d V c k W : Set _) :=
    Set.singleton_subset_iff.mpr (originalGenericOrbit_mem_uniformLiftingOpen f hL d V c k W hW)
  intro x
  have hx : x ∈ closure ({η} : Set (Orbit eo)) := by rw [hg.def]; trivial
  exact closure_mono hs hx

end FLT.Mazur.HilbertChart.AffineRestriction
