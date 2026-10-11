/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertEtaleGeometricLift

/-!
# Full étale chart intersections cover every original test point

Every geometric point of an original Picard test lifts to a full intersection
for a constructed étale translation base. Algebraic closures of the actual
test residue fields then prove coverage of all points, not only closed ones.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- Every original geometric test point lifts through one constructed full étale intersection. -/
theorem exists_orderedHilbert_etale_overlap_geometric_lift
    {K : Type} [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ T.left) :
    ∃ (i : SmoothHilbertTranslationIndex) (E : Over (Spec (.of R)))
      (b : E ⟶ smoothTranslationTest f i.1),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      Etale E.hom ∧ ∃ q : Spec (.of K) ⟶ (variableHilbertOverlap f i.2 E c T s).left,
        q ≫ (variableHilbertOverlapToTest f i.2 E c T s).left = p := by
  let a : Over.mk (p ≫ T.hom) ⟶ T := Over.homMk p
  obtain ⟨i, E, b, q, he, hq, _, _⟩ := exists_orderedHilbert_etale_geometric_lift f hL
    (p ≫ T.hom) ((relativeFppfSheaf f).obj.map a.op s)
  obtain ⟨z, hz, _⟩ := variableHilbertOverlap_lift f i.2 hL E
    ((relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)) T s a q hq
  exact ⟨i, E, b, he, z.left, congrArg Over.Hom.left hz.1⟩

/-- Constructed full étale intersections cover all original points, including nonclosed points. -/
theorem exists_orderedHilbert_etale_overlap_point (x : T.left) :
    ∃ (i : SmoothHilbertTranslationIndex) (E : Over (Spec (.of R)))
      (b : E ⟶ smoothTranslationTest f i.1),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      Etale E.hom ∧ ∃ y : (variableHilbertOverlap f i.2 E c T s).left,
        (variableHilbertOverlapToTest f i.2 E c T s).left y = x := by
  let K := AlgebraicClosure (T.left.residueField x)
  let g := Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K))
  obtain ⟨i, E, b, he, q, hq⟩ := exists_orderedHilbert_etale_overlap_geometric_lift
    f hL T s (g ≫ T.left.fromSpecResidueField x)
  refine ⟨i, E, b, he, q default, ?_⟩
  exact (congrArg (fun v : Spec (.of K) ⟶ T.left ↦ v default) hq).trans
    (T.left.fromSpecResidueField_apply x _)

end FLT.Mazur.HilbertChart
