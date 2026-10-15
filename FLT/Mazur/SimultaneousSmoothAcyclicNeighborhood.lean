/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SimultaneousSmoothHilbertParameters
public import FLT.Mazur.SmoothFiniteGeometricDiagram
public import FLT.Mazur.AcyclicDegreeGeometricSpread

/-!
# Simultaneous original acyclic classes on one constructed smooth neighborhood

For finitely many original Picard sections and an arbitrary geometric test,
construct a common affine smooth neighborhood, a single divisor degree and
actual original smooth translation coordinates. All translated sections
belong to the original acyclic degree locus on that whole neighborhood.
The translations are independent; this does not assert invariant orbit coverage.
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
  {T : Over (Spec (.of R))} {n : ℕ}
  (s : Fin n → (relativeFppfSheaf f).obj.obj (op T))
  {K : Type} [Field K] [IsAlgClosed K] {t : Spec (.of K) ⟶ Spec (.of R)}
  (b : Over.mk t ⟶ T)

/-- Finite original sections acquire actual common-degree acyclic translations smoothly locally. -/
theorem exists_simultaneous_smooth_acyclic_neighborhood :
    ∃ (d : ℕ) (i : Fin n → SmoothTranslationIndex)
      (W : Over (Spec (.of R))) (q : W ⟶ T) (z : Over.mk t ⟶ W)
      (r : ∀ j, W ⟶ smoothTranslationTest f (i j)),
      IsAffine W.left ∧ Smooth q.left ∧ z ≫ q = b ∧
      ∀ j, (relativeFppfSheaf f).obj.map q.op (s j) *
        (relativeFppfSheaf f).obj.map (r j).op (smoothTranslationClass f hL.2.1 (i j)) ∈
          (acyclicDegreePicardSubfunctor f d).obj (op W) := by
  obtain ⟨d, i, v, hv⟩ := exists_simultaneous_smooth_acyclic_degree f hL t
    (fun j ↦ (relativeFppfSheaf f).obj.map b.op (s j))
  let P (j : Fin n) := pullback (smoothTranslationTest f (i j)).hom T.hom
  let p (j : Fin n) : P j ⟶ T.left := pullback.snd _ _
  let a (j : Fin n) : Spec (.of K) ⟶ P j :=
    pullback.lift (v j).left b.left ((v j).w.trans b.w.symm)
  have ha (j : Fin n) : a j ≫ p j = b.left := pullback.lift_snd _ _ _
  obtain ⟨U, q, z, r, hU, hq, hz, hr, he⟩ :=
    SmoothFiniteGeometricDiagram.exists_common_affine P p b.left a ha
  let W : Over (Spec (.of R)) := Over.mk (q ≫ T.hom)
  let q' : W ⟶ T := Over.homMk q
  let z' : Over.mk t ⟶ W := Over.homMk z (by
    change z ≫ q ≫ T.hom = t
    rw [← Category.assoc, hz, b.w]
    rfl)
  let r' (j : Fin n) : W ⟶ smoothTranslationTest f (i j) :=
    Over.homMk (r j ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hr]
      rfl)
  have hzq : z' ≫ q' = b := Over.OverMorphism.ext hz
  have hzr (j : Fin n) : z' ≫ r' j = v j := by
    apply Over.OverMorphism.ext
    change z ≫ r j ≫ pullback.fst _ _ = (v j).left
    rw [← Category.assoc, he]
    exact pullback.lift_fst _ _ _
  let C (j : Fin n) : (relativeFppfSheaf f).obj.obj (op W) :=
    (relativeFppfSheaf f).obj.map q'.op (s j) *
      (relativeFppfSheaf f).obj.map (r' j).op (smoothTranslationClass f hL.2.1 (i j))
  have hC (j : Fin n) : (relativeFppfSheaf f).obj.map z'.op (C j) ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
    dsimp only [C]
    rw [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hzq,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hzr]
    exact hv j
  obtain ⟨W', u, w, hW', hu, hw, hmem⟩ :=
    exists_affine_acyclic_degree_spread f C (fun _ ↦ d) z' hC
  refine ⟨d, i, W', u ≫ q', w, fun j ↦ u ≫ r' j, hW',
    inferInstanceAs (Smooth (u.left ≫ q)), ?_, ?_⟩
  · rw [← Category.assoc, hw, hzq]
  · intro j
    simpa only [C, map_mul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      using hmem j

/-- The constructed neighborhood supplies actual original Hilbert maps for every section. -/
theorem exists_simultaneous_smooth_hilbert_neighborhood :
    ∃ (d : ℕ) (i : Fin n → SmoothTranslationIndex)
      (W : Over (Spec (.of R))) (q : W ⟶ T) (z : Over.mk t ⟶ W)
      (a : ∀ j, W ⟶ variableHilbertTest f d (smoothTranslationTest f (i j))),
      IsAffine W.left ∧ Smooth q.left ∧ z ≫ q = b ∧
      ∀ j, (relativeFppfSheaf f).obj.map (a j).op
        (variableChartSection f hL d (smoothTranslationTest f (i j))
          (smoothTranslationClass f hL.2.1 (i j))) =
            (relativeFppfSheaf f).obj.map q.op (s j) := by
  obtain ⟨d, i, W, q, z, r, hW, hq, hz, hr⟩ :=
    exists_simultaneous_smooth_acyclic_neighborhood f hL s b
  exact ⟨d, i, W, q, z, fun j ↦ acyclicTranslationLift f hL d _ _
    ((relativeFppfSheaf f).obj.map q.op (s j)) (r j) (hr j), hW, hq, hz,
    fun j ↦ acyclicTranslationLift_class f hL d _ _ _ (r j) (hr j)⟩

/-- The constructed simultaneous neighborhoods cover every original test point. -/
theorem exists_simultaneous_smooth_hilbert_point (x : T.left) :
    ∃ (d : ℕ) (i : Fin n → SmoothTranslationIndex)
      (W : Over (Spec (.of R))) (q : W ⟶ T)
      (a : ∀ j, W ⟶ variableHilbertTest f d (smoothTranslationTest f (i j))),
      IsAffine W.left ∧ Smooth q.left ∧ x ∈ Set.range q.left ∧
      ∀ j, (relativeFppfSheaf f).obj.map (a j).op
        (variableChartSection f hL d (smoothTranslationTest f (i j))
          (smoothTranslationClass f hL.2.1 (i j))) =
            (relativeFppfSheaf f).obj.map q.op (s j) := by
  let K := AlgebraicClosure (T.left.residueField x)
  let g := Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K))
  let t := g ≫ T.left.fromSpecResidueField x ≫ T.hom
  let b : Over.mk t ⟶ T := Over.homMk (g ≫ T.left.fromSpecResidueField x)
  obtain ⟨d, i, W, q, z, a, hW, hq, hz, ha⟩ :=
    exists_simultaneous_smooth_hilbert_neighborhood f hL s b
  refine ⟨d, i, W, q, a, hW, hq, ⟨z.left (default : Spec (.of K)), ?_⟩, ha⟩
  exact (congrArg (fun v : Over.mk t ⟶ T ↦ v.left (default : Spec (.of K))) hz).trans
    (T.left.fromSpecResidueField_apply x _)

end FLT.Mazur.HilbertChart
