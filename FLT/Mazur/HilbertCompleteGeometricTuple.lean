/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFullRelationOrderedPoints
public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation
public import FLT.Mazur.RelativeCompleteGeometricTuple

/-!
# Complete original geometric relation tuples and affine neighborhoods

Every original geometric source point has an actual ordered-point test
covering the entire geometric relation fiber exactly once. It factors through
an affine etale neighborhood in the constructed ordered-point scheme. This
retains both original endpoints, but completeness is asserted only at the
distinguished geometric fiber, not throughout that neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

open RelativeOrderedTuples
local notation "E" => fullRelationOverFirst f hL d V c k
variable {K : Type} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ A.left)

local instance originalOrderedSource_quasiCompact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact (p).left)

/-- An actual original ordered-point test exhausts the entire geometric relation fiber. -/
theorem exists_fullRelation_complete_tuple :
    ∃ (n : ℕ) (a : Over.mk b ⟶ fullRelationOrderedPoints f hL d V c k n),
      Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) a i default) :=
  exists_complete_geometric_tuple E b

/-- The complete original test lies in an actual affine etale ordered-point neighborhood. -/
theorem exists_fullRelation_complete_affine_tuple :
    ∃ (n : ℕ) (a : Over.mk b ⟶ fullRelationOrderedPoints f hL d V c k n)
      (U : Scheme) (u : U ⟶ (fullRelationOrderedPoints f hL d V c k n).left)
      (z : Spec (.of K) ⟶ U),
      Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) a i default) ∧
      IsAffine U ∧ IsOpenImmersion u ∧
      Etale (u ≫ (fullRelationOrderedPoints f hL d V c k n).hom) ∧
      z ≫ u = a.left ∧ z ≫ u ≫ (fullRelationOrderedPoints f hL d V c k n).hom = b := by
  obtain ⟨n, a, ha⟩ := exists_fullRelation_complete_tuple f hL d V c k b
  obtain ⟨U, u, z, hU, hu, hz, _⟩ :=
    EtaleFiniteGeometricDiagram.exists_affine_factor a.left ⊤ (by trivial)
  refine ⟨n, a, U, u, z, ha, hU, hu, inferInstance, hz, ?_⟩
  rw [← Category.assoc, hz]
  exact a.w

end FLT.Mazur.HilbertChart.AffineRestriction
