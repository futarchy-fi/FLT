/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertFiniteRelationFibers
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import FLT.Mazur.RelativeRelationOrbit

/-!
# Affine envelopes for the original full Hilbert intersections

For affine original tests and affine étale translations, the full intersection
has an affine product envelope. Its entire finite fiber fits in one affine
neighborhood inside any prescribed open. The original full chart orbits are
also finite; no invariant affine source neighborhood is inferred from this.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

omit [Algebra.FiniteType ℤ R] [Etale V.hom] in
/-- The full relation's original test/base product is an affine envelope on affine tests. -/
theorem variableHilbertOverlap_envelope_affine
    (U : Over (Spec (.of R))) [IsAffine U.left] : IsAffine (prod U V).left :=
  IsAffine.of_isIso (Over.prodLeftIsoPullback U V).hom

/-- One affine neighborhood contains the entire original intersection fiber. -/
theorem exists_variableHilbertOverlap_fiber_affine_neighborhood
    (U : Over (Spec (.of R))) [IsAffine U.left]
    (s : (relativeFppfSheaf f).obj.obj (op U)) (x : U.left)
    (W : (variableHilbertOverlap f d V c U s).left.Opens)
    (hW : (variableHilbertOverlapToTest f d V c U s).left ⁻¹' {x} ⊆ W) :
    ∃ A : (variableHilbertOverlap f d V c U s).left.Opens,
      IsAffineOpen A ∧ (variableHilbertOverlapToTest f d V c U s).left ⁻¹' {x} ⊆ A ∧
        A ≤ W := by
  let _ := variableHilbertOverlap_envelope_affine V U
  exact AffineEnvelopeFiniteNeighborhood.exists_affineOpen
    (variableHilbertOverlapArrow f d V c U s).left W _
    (variableHilbertOverlapToTest_finite_fiber f d V c U s x) hW

variable {L : X.Modules} (hL : AmpleLineBundle L)

/-- Every original full chart orbit is finite, with all independent base coordinates retained. -/
theorem variableChartOrbit_finite (x : (variableHilbertTest f d V).left) :
    {y | projection (variableChartEquivalenceRelation f hL d V c) y =
      projection (variableChartEquivalenceRelation f hL d V c) x}.Finite := by
  apply ((variableChartRelationFst_finite_fiber f d V c hL x).image
    (variableChartRelationSnd f hL d V c).left).subset
  intro y hy
  obtain ⟨a, ha, hb⟩ := (projection_eq_iff
    (variableChartEquivalenceRelation f hL d V c) x y).mp hy.symm
  exact ⟨a, ha, hb⟩

end FLT.Mazur.HilbertChart
