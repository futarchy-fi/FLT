/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTestAffineFullFiber
public import FLT.Mazur.GeometricPointCoverCriterion

/-!
# Constructed original full fibers over every point of every original test

Algebraic closures of the actual residue fields convert the geometric
construction into coverage of arbitrary original points. Each covering
neighborhood is étale and carries the unchanged original section. Fullness
is retained at a point of its affine parameter chart, not asserted open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

include hL in
/-- Every original point, including nonclosed points, is met by a constructed full-fiber chart. -/
theorem original_test_full_fiber_covers (x : T.left) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V),
      IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left, let _ := hk
      ∃ (Y : Over (Spec (.of R))) (q : Y ⟶ T) (r : Y ⟶ A) (y : Y.left),
        Etale q.left ∧ q.left y = x ∧
        (relativeFppfSheaf f).obj.map q.op s =
          (relativeFppfSheaf f).obj.map r.op (sectionAt f hL d V c k) ∧
        r.left y ∈ fullEnvelopeLocus f hL d V c k := by
  let K := AlgebraicClosure (T.left.residueField x)
  let g : Spec (.of K) ⟶ Spec (T.left.residueField x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K))
  let p : Spec (.of K) ⟶ T.left := g ≫ T.left.fromSpecResidueField x
  let b : Over.mk (p ≫ T.hom) ⟶ T := Over.homMk p
  obtain ⟨d, V, c, A, k, hV, he, hA, hk, Y, q, r, z, hq, hz, hs, hf⟩ :=
    exists_original_test_affine_full_fiber f hL T s b
  let η : Spec (.of K) := default
  refine ⟨d, V, c, A, k, hV, he, hA, hk, Y, q, r, z.left η, hq, ?_, hs, hf⟩
  have hp : p η = x := T.left.fromSpecResidueField_apply x _
  exact (congrArg (fun a : Over.mk (p ≫ T.hom) ⟶ T ↦ a.left η) hz).trans hp

end FLT.Mazur.HilbertChart.AffineRestriction
