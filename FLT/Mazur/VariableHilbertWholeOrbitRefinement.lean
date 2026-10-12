/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertWholeOrbitAffine
public import FLT.Mazur.AffineOpenFiniteRefinement

/-!
# Compatible affine refinements retaining the entire original orbit

The whole finite source set can be kept inside any prescribed ambient open.
Pairwise refinements preserve every original orbit point and the common ambient
support. These statements do not assert invariance under the full relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]

variable {L : X.Modules} (hL : AmpleLineBundle L)
include hL

/-- Every finite source set has an affine refinement inside any prescribed containing open. -/
theorem exists_variableHilbert_finite_affine_refinement
    (t : Set (variableHilbertTest f d V).left) (ht : t.Finite)
    (O : (variableHilbertTest f d V).left.Opens) (htO : t ⊆ O) :
    ∃ (U : X.affineOpens) (W : (variableHilbertTest f d V).left.Opens),
      IsAffineOpen W ∧ t ⊆ W ∧ W ≤ O ∧ W ≤ commonAmbientSourceOpen f d V U := by
  obtain ⟨U, A, hA, htA, hAU⟩ :=
    exists_variableHilbert_finite_affine_neighborhood f d V hL t ht
  obtain ⟨W, hW, htW, hWA⟩ :=
    AffineEnvelopeFiniteNeighborhood.refine_affineOpen A hA O t ht htA htO
  exact ⟨U, W, hW, htW, hWA.trans inf_le_right,
    (hWA.trans inf_le_left).trans hAU⟩

/-- Two affine neighborhoods of the full original orbit have a common affine refinement. -/
theorem exists_variableHilbert_orbit_affine_inter_refinement [Etale V.hom]
    (c : (relativeFppfSheaf f).obj.obj (op V)) (x : (variableHilbertTest f d V).left)
    (A B : (variableHilbertTest f d V).left.Opens)
    (hA : {y | projection (variableChartEquivalenceRelation f hL d V c) y =
      projection (variableChartEquivalenceRelation f hL d V c) x} ⊆ A)
    (hB : {y | projection (variableChartEquivalenceRelation f hL d V c) y =
      projection (variableChartEquivalenceRelation f hL d V c) x} ⊆ B) :
    ∃ (U : X.affineOpens) (W : (variableHilbertTest f d V).left.Opens),
      IsAffineOpen W ∧
      {y | projection (variableChartEquivalenceRelation f hL d V c) y =
        projection (variableChartEquivalenceRelation f hL d V c) x} ⊆ W ∧
      W ≤ A ⊓ B ∧ W ≤ commonAmbientSourceOpen f d V U :=
  exists_variableHilbert_finite_affine_refinement f d V hL _
    (variableChartOrbit_finite f d V c hL x) (A ⊓ B) (fun _ hy ↦ ⟨hA hy, hB hy⟩)

end FLT.Mazur.HilbertChart
