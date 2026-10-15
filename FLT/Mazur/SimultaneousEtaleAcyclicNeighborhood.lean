/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SimultaneousSmoothAcyclicNeighborhood
public import FLT.Mazur.SmoothAffineEtaleRefinement

/-!
# Simultaneous acyclic translations on constructed étale neighborhoods

For finite original Picard sections on an affine test, refine the constructed
smooth neighborhood étale locally. All translations have one degree and
satisfy the acyclic divisor condition on the entire new neighborhood.
The base geometric map is retained; the selected smooth coordinates may change.
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
  {T : Over (Spec (.of R))} [IsAffine T.left] {n : ℕ}
  (s : Fin n → (relativeFppfSheaf f).obj.obj (op T))
  {K : Type} [Field K] [IsAlgClosed K] {t : Spec (.of K) ⟶ Spec (.of R)}
  (b : Over.mk t ⟶ T)

/-- Finite original sections acquire common-degree acyclic translations étale locally. -/
theorem exists_simultaneous_etale_acyclic_neighborhood :
    ∃ (d : ℕ) (i : Fin n → SmoothTranslationIndex)
      (W : Over (Spec (.of R))) (q : W ⟶ T) (z : Over.mk t ⟶ W)
      (r : ∀ j, W ⟶ smoothTranslationTest f (i j)),
      IsAffine W.left ∧ Etale q.left ∧ z ≫ q = b ∧
      ∀ j, (relativeFppfSheaf f).obj.map q.op (s j) *
        (relativeFppfSheaf f).obj.map (r j).op (smoothTranslationClass f hL.2.1 (i j)) ∈
          (acyclicDegreePicardSubfunctor f d).obj (op W) := by
  obtain ⟨d, i, U, q, z, r, hU, hq, hz, hr⟩ :=
    exists_simultaneous_smooth_acyclic_neighborhood f hL s b
  obtain ⟨E, e, v, w, hE, he, hv, hw⟩ :=
    SmoothAffineEtaleRefinement.exists_affine_lift q.left b.left z.left
      (congrArg Over.Hom.left hz)
  let W : Over (Spec (.of R)) := Over.mk (e ≫ T.hom)
  let q' : W ⟶ T := Over.homMk e
  let a : W ⟶ U := Over.homMk v (by
    rw [← q.w, ← Category.assoc, hv]
    rfl)
  let z' : Over.mk t ⟶ W := Over.homMk w (by
    change w ≫ e ≫ T.hom = t
    rw [← Category.assoc, hw, b.w]
    rfl)
  have haq : a ≫ q = q' := Over.OverMorphism.ext hv
  refine ⟨d, i, W, q', z', fun j ↦ a ≫ r j, hE, he, Over.OverMorphism.ext hw, ?_⟩
  intro j
  have h := (acyclicDegreePicardSubfunctor f d).map a.op (hr j)
  change (relativeFppfSheaf f).obj.map a.op
    ((relativeFppfSheaf f).obj.map q.op (s j) *
      (relativeFppfSheaf f).obj.map (r j).op (smoothTranslationClass f hL.2.1 (i j))) ∈
        (acyclicDegreePicardSubfunctor f d).obj (op W) at h
  simpa only [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, haq]
    using h

/-- The étale neighborhood supplies original Hilbert maps of one common degree for all sections. -/
theorem exists_simultaneous_etale_hilbert_neighborhood :
    ∃ (d : ℕ) (i : Fin n → SmoothTranslationIndex)
      (W : Over (Spec (.of R))) (q : W ⟶ T) (z : Over.mk t ⟶ W)
      (a : ∀ j, W ⟶ variableHilbertTest f d (smoothTranslationTest f (i j))),
      IsAffine W.left ∧ Etale q.left ∧ z ≫ q = b ∧
      ∀ j, (relativeFppfSheaf f).obj.map (a j).op
        (variableChartSection f hL d (smoothTranslationTest f (i j))
          (smoothTranslationClass f hL.2.1 (i j))) =
            (relativeFppfSheaf f).obj.map q.op (s j) := by
  obtain ⟨d, i, W, q, z, r, hW, hq, hz, hr⟩ :=
    exists_simultaneous_etale_acyclic_neighborhood f hL s b
  exact ⟨d, i, W, q, z, fun j ↦ acyclicTranslationLift f hL d _ _
    ((relativeFppfSheaf f).obj.map q.op (s j)) (r j) (hr j), hW, hq, hz,
    fun j ↦ acyclicTranslationLift_class f hL d _ _ _ (r j) (hr j)⟩

end FLT.Mazur.HilbertChart
