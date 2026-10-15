/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertWholeOrbitAffine

/-!
# Constructed affine retention of all equal-class geometric parameters

One affine open of the original variable Hilbert chart retains every map
with the same original Picard class as a given geometric parameter. The
open is constructed from the finite original orbit; no retained family is
assumed and no invariance of the affine open is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- Equal original sheaf classes give the same original orbit at every test point. -/
theorem variableHilbertPoint_same_orbit {T : Over (Spec (.of R))}
    (a b : T ⟶ variableHilbertTest f d V)
    (h : (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) =
      (relativeFppfSheaf f).obj.map b.op (variableChartSection f hL d V c)) (x : T.left) :
    projection (variableChartEquivalenceRelation f hL d V c) (a.left x) =
      projection (variableChartEquivalenceRelation f hL d V c) (b.left x) := by
  obtain ⟨q, hq, _⟩ := variableChartRelation_lift f hL d V c a b h
  apply (projection_eq_iff _ _ _).mpr
  exact ⟨q.left x, congrArg (fun g : T ⟶ variableHilbertTest f d V ↦ g.left x) hq.1,
    congrArg (fun g : T ⟶ variableHilbertTest f d V ↦ g.left x) hq.2⟩

/-- A constructed original affine open retains every equal-class geometric map in full. -/
theorem exists_affine_retaining_geometric_class [IsAffine V.left] [Etale V.hom]
    {K : Type} [Field K] {t : Spec (.of K) ⟶ Spec (.of R)}
    (b : Over.mk t ⟶ variableHilbertTest f d V) :
    ∃ W : (variableHilbertTest f d V).left.Opens, IsAffineOpen W ∧
      Set.range b.left ⊆ W ∧
      ∀ a : Over.mk t ⟶ variableHilbertTest f d V,
        (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) =
          (relativeFppfSheaf f).obj.map b.op (variableChartSection f hL d V c) →
        Set.range a.left ⊆ W := by
  obtain ⟨_, W, hW, ho, _⟩ := exists_variableHilbert_orbit_affine_neighborhood
    f d V hL c (b.left (default : Spec (.of K)))
  have hret (a : Over.mk t ⟶ variableHilbertTest f d V)
      (ha : (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) =
        (relativeFppfSheaf f).obj.map b.op (variableChartSection f hL d V c)) :
      Set.range a.left ⊆ W := by
    rintro _ ⟨x, rfl⟩
    apply ho
    have hx : x = (default : Spec (.of K)) :=
      Subsingleton.elim (α := Spec (.of K)) x default
    rw [← hx]
    exact variableHilbertPoint_same_orbit f hL d V c a b ha x
  exact ⟨W, hW, hret b rfl, hret⟩

end FLT.Mazur.HilbertChart
