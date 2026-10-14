/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalUniversalScaling
public import FLT.Mazur.PolygonInfinitesimalEdgeCoordinates

/-!
# Full Laurent coordinates of universal polygon scaling

The restriction of the constructed whole-polygon scaling to every full
edge is the variable Laurent scaling followed by coefficient projection.
This computation retains the original coefficient ring and all nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

omit [Fact (IsNilpotent t)] in
/-- Multiplication of the independent full Laurent coordinates as a map of schemes. -/
def universalEdgeScaling : branchTorus R[T;T⁻¹] ⟶ branchTorus R :=
  (edgeScalingIso (PolygonUniversalScaling.u (R := R))).hom ≫
    Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap
      (LaurentPolynomial.C : R →+* R[T;T⁻¹])))

/-- Every full edge of the universal family carries the literal Laurent scaling map. -/
@[reassoc] theorem edge_universalScaling (i : Fin n) :
    edge R[T;T⁻¹] (LaurentPolynomial.C t) n h i ≫ universalScaling R t n h =
      universalEdgeScaling R ≫ edge R t n h i := by
  rw [universalScaling, edge_scaling_assoc, scalingParameterProjection,
    universalEdgeScaling, Category.assoc]
  have he := (edge_parameter_isPullback t n h
    (LaurentPolynomial.C : R →+* R[T;T⁻¹]) (LaurentPolynomial.C t) rfl i).w
  exact congrArg (_ ≫ ·) he.symm

end FLT.Mazur.PolygonInfinitesimal
