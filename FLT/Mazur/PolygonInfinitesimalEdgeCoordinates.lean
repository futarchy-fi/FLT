/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalScalingNaturality
public import FLT.Mazur.CartesianFiniteFibers

/-!
# Full Laurent edge coordinates in the original infinitesimal polygon

The original outgoing edge gives an open Laurent chart over all coefficient
rings. Its coefficient squares are cartesian and its scaling is the literal
Laurent-coordinate scaling, before passing to the reduced fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
universe u
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- The original outgoing Laurent edge, including its full coefficient scheme. -/
def edge (i : Fin n) : branchTorus R ⟶ scheme R t n h :=
  leftBranchOpen R t ≫ chart R t n h i

/-- Every full Laurent edge is an actual open chart of the original scheme. -/
instance edge_isOpenImmersion (i : Fin n) : IsOpenImmersion (edge R t n h i) :=
  inferInstanceAs (IsOpenImmersion (leftBranchOpen R t ≫ chart R t n h i))

/-- Its structure morphism retains the actual original coefficient map. -/
@[reassoc] theorem edge_toBase (i : Fin n) :
    edge R t n h i ≫ toBase R t n h =
      Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) := by
  rw [edge, Category.assoc, chart_toBase, leftBranchOpen_base]

/-- Whole-polygon scaling restricts to the full original Laurent edge scaling. -/
@[reassoc] theorem edge_scaling (i : Fin n) (a : Rˣ) :
    edge R t n h i ≫ scaling R t n h a =
      (edgeScalingIso a).hom ≫ edge R t n h i := by
  rw [edge, Category.assoc, chart_scaling, leftBranch_reciprocalScaling_assoc]

variable (S : Type u) [CommRing S] [Algebra R S]
  [Fact (IsNilpotent (algebraMap R S t))]

/-- The original edge inclusion commutes with the full coefficient projection. -/
@[reassoc] theorem edge_coefficientProjection (i : Fin n) :
    edge S (algebraMap R S t) n h i ≫ coefficientProjection R S t n h =
      edgeCoefficient R S ≫ edge R t n h i := by
  rw [edge, Category.assoc, chart_coefficientProjection, leftBranch_coefficient_assoc, edge]

/-- The full Laurent edge is exactly the coefficient pullback of the original edge. -/
theorem edge_coefficient_isPullback (i : Fin n) :
    IsPullback (edgeCoefficient R S) (edge S (algebraMap R S t) n h i)
      (edge R t n h i) (coefficientProjection R S t n h) := by
  apply ((coefficientProjection_isPullback R S t n h).paste_vert_iff
    (edge_coefficientProjection R t n h S i).symm).mp
  simpa only [edge_toBase] using edgeCoefficient_isPullback R S

variable {R S} in
omit [Algebra R S] [Fact (IsNilpotent (algebraMap R S t))] in
/-- The full edge square for a specified coefficient map and its actual target parameter. -/
theorem edge_parameter_isPullback (f : R →+* S) (s : S) [Fact (IsNilpotent s)]
    (hs : f t = s) (i : Fin n) :
    IsPullback (Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f)))
      (edge S s n h i) (edge R t n h i) (parameterProjection f t s hs n h) := by
  subst s
  let _ := f.toAlgebra
  exact edge_coefficient_isPullback R t n h S i

end FLT.Mazur.PolygonInfinitesimal
