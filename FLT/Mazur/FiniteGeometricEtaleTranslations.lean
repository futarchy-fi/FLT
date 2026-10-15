/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryPicardEtaleTranslation
public import FLT.Mazur.EtaleFiniteGeometricAffine

/-!
# Common original étale parameters for independent geometric classes

Finitely many arbitrary geometric classes acquire independent original
translations on one affine étale parameter scheme, with one divisor degree.
The common geometric lift preserves each prescribed class. No extension of
any input class to the original coefficient base is supplied.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Spec (.of R))
  {n : ℕ} (s : Fin n → (relativeFppfSheaf f).obj.obj (op (Over.mk t)))

include hL in
/-- Independent geometric classes have common-degree translations on one original étale test. -/
theorem exists_finite_geometric_etale_translations :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : Fin n → (relativeFppfSheaf f).obj.obj (op V)) (v : Over.mk t ⟶ V),
      IsAffine V.left ∧ Etale V.hom ∧ ∀ j,
      s j * (relativeFppfSheaf f).obj.map v.op (c j) ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  obtain ⟨d, i, v, hv⟩ := exists_simultaneous_smooth_acyclic_degree f hL t s
  have h (j : Fin n) := exists_etale_translation_of_geometric_acyclicity f d
    (smoothTranslationTest f (i j)) (smoothTranslationClass f hL.2.1 (i j))
      (s j) (v j) (hv j)
  choose E r z hE he hz using h
  let _ (j : Fin n) : Etale (E j).hom := he j
  obtain ⟨V, q, w, a, hV, hq, hw, ha, hwa⟩ :=
    EtaleFiniteGeometricDiagram.exists_common_affine (fun j ↦ (E j).left)
      (fun j ↦ (E j).hom) t (fun j ↦ (z j).left) (fun j ↦ (z j).w)
  let W : Over (Spec (.of R)) := Over.mk q
  let w' : Over.mk t ⟶ W := Over.homMk w hw
  let a' (j : Fin n) : W ⟶ E j := Over.homMk (a j) (ha j)
  let c (j : Fin n) := (relativeFppfSheaf f).obj.map (a' j ≫ r j).op
    (smoothTranslationClass f hL.2.1 (i j))
  have heq (j : Fin n) : w' ≫ a' j = z j := Over.OverMorphism.ext (hwa j)
  refine ⟨d, W, c, w', hV, hq, fun j ↦ ?_⟩
  simpa only [c, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← Category.assoc, heq] using hz j

/-- Every member is represented in an original Hilbert chart with the same étale parameters. -/
theorem exists_finite_geometric_etale_hilbert_lifts :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : Fin n → (relativeFppfSheaf f).obj.obj (op V))
      (a : Fin n → (Over.mk t ⟶ variableHilbertTest f d V)),
      IsAffine V.left ∧ Etale V.hom ∧ ∀ j,
      (relativeFppfSheaf f).obj.map (a j).op (variableChartSection f hL d V (c j)) = s j := by
  obtain ⟨d, V, c, v, hV, he, hv⟩ := exists_finite_geometric_etale_translations f hL t s
  exact ⟨d, V, c, fun j ↦ acyclicTranslationLift f hL d V (c j) (s j) v (hv j), hV, he,
    fun j ↦ acyclicTranslationLift_class f hL d V (c j) (s j) v (hv j)⟩

end FLT.Mazur.HilbertChart
