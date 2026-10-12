/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientDeterminantTarget
public import FLT.Mazur.VariableHilbertCommonAmbientAtlas

/-!
# A single affine neighborhood for the entire original Hilbert orbit

The constructed ample determinant target removes the target-ampleness premise.
Every finite subset supported in one original affine ambient lies in one affine
source neighborhood. Original full relation orbits are retained without assuming
that the resulting affine source neighborhood is invariant.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]

/-- A whole finite source set in one original ambient admits one affine source neighborhood. -/
theorem exists_commonAmbient_affine_neighborhood (U : X.affineOpens)
    (t : Set (variableHilbertTest f d V).left) (ht : t.Finite)
    (hU : t ⊆ commonAmbientSourceOpen f d V U) :
    ∃ W : (variableHilbertTest f d V).left.Opens,
      IsAffineOpen W ∧ t ⊆ W ∧ W ≤ commonAmbientSourceOpen f d V U :=
  exists_commonAmbient_affine_of_target_ample f d V U
    (commonAmbientTargetDeterminantLine f d U V)
    (commonAmbientTargetDeterminantLine_ample f d U V) t ht hU

variable {L : X.Modules} (hL : AmpleLineBundle L)

include hL in
/-- Every finite subset of the unrestricted source fits in an actual affine neighborhood. -/
theorem exists_variableHilbert_finite_affine_neighborhood
    (t : Set (variableHilbertTest f d V).left) (ht : t.Finite) :
    ∃ (U : X.affineOpens) (W : (variableHilbertTest f d V).left.Opens),
      IsAffineOpen W ∧ t ⊆ W ∧ W ≤ commonAmbientSourceOpen f d V U := by
  obtain ⟨U, hU⟩ := exists_commonAmbientSourceOpen f d V hL t ht
  obtain ⟨W, hW, htW, hWU⟩ := exists_commonAmbient_affine_neighborhood f d V U t ht hU
  exact ⟨U, W, hW, htW, hWU⟩

include hL in
/-- One affine source neighborhood contains the WHOLE original full relation orbit. -/
theorem exists_variableHilbert_orbit_affine_neighborhood [Etale V.hom]
    (c : (relativeFppfSheaf f).obj.obj (op V)) (x : (variableHilbertTest f d V).left) :
    ∃ (U : X.affineOpens) (W : (variableHilbertTest f d V).left.Opens),
      IsAffineOpen W ∧
      {y | projection (variableChartEquivalenceRelation f hL d V c) y =
        projection (variableChartEquivalenceRelation f hL d V c) x} ⊆ W ∧
      W ≤ commonAmbientSourceOpen f d V U :=
  exists_variableHilbert_finite_affine_neighborhood f d V hL _
    (variableChartOrbit_finite f d V c hL x)

end FLT.Mazur.HilbertChart
