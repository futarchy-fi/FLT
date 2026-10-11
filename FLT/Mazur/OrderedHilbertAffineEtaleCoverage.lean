/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertEtaleGeometricLift
public import FLT.Mazur.VariableHilbertAffinePointRefinement

/-!
# Affine étale translation charts cover original Picard tests

Refine the constructed translation neighborhoods affinely while retaining
the original class. Their full intersections still cover every point of
every original test. Affineness refers to the translation base; neither
finiteness over the original base nor quotient effectivity is inferred.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)

/-- Every geometric original class has a chart with an actual affine étale translation base. -/
theorem exists_orderedHilbert_affine_etale_geometric_lift
    {K : Type} [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ Spec (.of R))
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk g))) :
    ∃ (i : SmoothHilbertTranslationIndex) (E : Over (Spec (.of R)))
      (b : E ⟶ smoothTranslationTest f i.1)
      (q : Over.mk g ⟶ variableHilbertTest f i.2 E),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      IsAffine E.left ∧ Etale E.hom ∧ variableHilbertPoint f i.2 hL E c _ q = s := by
  obtain ⟨i, V, b, p, he, hp, _, _⟩ := exists_orderedHilbert_etale_geometric_lift f hL g s
  let _ := he
  obtain ⟨E, j, q, ha, _, hj, _, hq⟩ := exists_variableHilbert_affine_class_refinement
    f i.2 V g p hL ((relativeFppfSheaf f).obj.map b.op
      (smoothTranslationClass f hL.2.1 i.1))
  refine ⟨i, E, j ≫ b, q, ha, hj, ?_⟩
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hq.trans hp

/-- Every geometric test point lifts to the original full intersection of an affine étale chart. -/
theorem exists_orderedHilbert_affine_etale_overlap_geometric_lift
    (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
    {K : Type} [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ T.left) :
    ∃ (i : SmoothHilbertTranslationIndex) (E : Over (Spec (.of R)))
      (b : E ⟶ smoothTranslationTest f i.1),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      IsAffine E.left ∧ Etale E.hom ∧
        ∃ q : Spec (.of K) ⟶ (variableHilbertOverlap f i.2 E c T s).left,
          q ≫ (variableHilbertOverlapToTest f i.2 E c T s).left = p := by
  let a : Over.mk (p ≫ T.hom) ⟶ T := Over.homMk p
  obtain ⟨i, E, b, q, ha, he, hq⟩ := exists_orderedHilbert_affine_etale_geometric_lift
    f hL (p ≫ T.hom) ((relativeFppfSheaf f).obj.map a.op s)
  obtain ⟨z, hz, _⟩ := variableHilbertOverlap_lift f i.2 hL E
    ((relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)) T s a q hq
  exact ⟨i, E, b, ha, he, z.left, congrArg Over.Hom.left hz.1⟩

/-- Full intersections with affine étale translations cover nonclosed as well as closed points. -/
theorem exists_orderedHilbert_affine_etale_overlap_point
    (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T)) (x : T.left) :
    ∃ (i : SmoothHilbertTranslationIndex) (E : Over (Spec (.of R)))
      (b : E ⟶ smoothTranslationTest f i.1),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      IsAffine E.left ∧ Etale E.hom ∧
        ∃ y : (variableHilbertOverlap f i.2 E c T s).left,
          (variableHilbertOverlapToTest f i.2 E c T s).left y = x := by
  let K := AlgebraicClosure (T.left.residueField x)
  let g := Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K))
  obtain ⟨i, E, b, ha, he, q, hq⟩ :=
    exists_orderedHilbert_affine_etale_overlap_geometric_lift f hL T s
      (g ≫ T.left.fromSpecResidueField x)
  refine ⟨i, E, b, ha, he, q default, ?_⟩
  exact (congrArg (fun v : Spec (.of K) ⟶ T.left ↦ v default) hq).trans
    (T.left.fromSpecResidueField_apply x _)

end FLT.Mazur.HilbertChart
