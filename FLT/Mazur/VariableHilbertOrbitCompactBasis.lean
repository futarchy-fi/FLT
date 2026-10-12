/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSaturatedRefinement
public import Mathlib.Topology.Bases

/-!
# Compact open neighborhoods in the original full Hilbert orbit space

Every quotient open refines to the exact image of a whole-orbit affine source
neighborhood in one original common ambient. These images form a compact open
basis of the original quotient topology; no affine quotient model is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "e" => variableChartEquivalenceRelation f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c

/-- Any quotient neighborhood refines to the compact image of a whole-orbit affine open. -/
theorem exists_variableHilbert_orbit_compact_refinement
    (O : Opens (Orbit e)) (x : (variableHilbertTest f d V).left) (hx : projection e x ∈ O) :
    ∃ (U : X.affineOpens) (W : (variableHilbertTest f d V).left.Opens),
      IsAffineOpen W ∧ {y | projection e y = projection e x} ⊆ W ∧
      W ≤ commonAmbientSourceOpen f d V U ∧
      projection e x ∈ orbitImageOpen e (q).left.isOpenMap W ∧
      orbitImageOpen e (q).left.isOpenMap W ≤ O ∧
      IsCompact ((orbitImageOpen e (q).left.isOpenMap W : Opens (Orbit e)) : Set (Orbit e)) := by
  obtain ⟨U, W, hW, htW, hWU, hWB⟩ :=
    exists_variableHilbert_saturated_affine_refinement f hL d V c (pullOpen e O) x hx
  refine ⟨U, W, hW, htW, hWU, ⟨x, htW rfl, rfl⟩, ?_,
    orbitImageOpen_isCompact e (q).left.isOpenMap W hW⟩
  rintro z ⟨y, hy, rfl⟩
  exact hWB (le_saturateOpen e (q).left.isOpenMap W hy)

/-- Exact original quotient images of affine source opens supported in one original ambient. -/
def variableHilbertOrbitBasis : Set (Set (Orbit e)) :=
  {B | ∃ (U : X.affineOpens) (W : (variableHilbertTest f d V).left.Opens),
    IsAffineOpen W ∧ W ≤ commonAmbientSourceOpen f d V U ∧
      B = projection e '' (W : Set (variableHilbertTest f d V).left)}

/-- These actual affine-generated quotient neighborhoods form a topological basis. -/
theorem variableHilbertOrbitBasis_isBasis :
    IsTopologicalBasis (variableHilbertOrbitBasis f hL d V c) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨U, W, _, _, rfl⟩
    exact (orbitImageOpen e (q).left.isOpenMap W).isOpen
  · intro z O hz hO
    obtain ⟨x, rfl⟩ := projection_surjective e z
    obtain ⟨U, W, hW, _, hWU, hx, hWO, _⟩ :=
      exists_variableHilbert_orbit_compact_refinement f hL d V c ⟨O, hO⟩ x hz
    exact ⟨_, ⟨U, W, hW, hWU, rfl⟩, hx, hWO⟩

omit [IsAffine V.left] [Etale V.hom] in
/-- Every member of the constructed basis is compact in the original orbit topology. -/
theorem variableHilbertOrbitBasis_isCompact (B : Set (Orbit e))
    (hB : B ∈ variableHilbertOrbitBasis f hL d V c) : IsCompact B := by
  obtain ⟨U, W, hW, _, rfl⟩ := hB
  exact hW.isCompact.image (projection_continuous e)

end FLT.Mazur.HilbertChart
