/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGeometricEtaleTranslations
public import FLT.Mazur.DisjointSectionGeometricTranslation

/-!
# Constructed translations on a whole split geometric fiber

For a complete finite disjoint section cover, independent geometric Picard
classes have one translation on the full source after an affine étale change
of the splitting base. Every whole lift over the retained base map is translated to an acyclic class
of the same degree. Neither a global extension nor branch translations are
inputs. Independent lifts of the new splitting base over R remain separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {E U : Over (Spec (.of R))} [IsAffine U.left]
  (p : E ⟶ U) {n : ℕ} (a : Fin n → (U ⟶ E))
  [∀ i, IsOpenImmersion (a i).left]
  (ha : ∀ i, a i ≫ p = 𝟙 U)
  (hc : ∀ x : E.left, ∃ i, (a i).left (p.left x) = x)
  (hd : Pairwise (fun i j ↦ Disjoint (Set.range (a i).left) (Set.range (a j).left)))
  {K : Type} [Field K] [IsAlgClosed K] {t : Spec (.of K) ⟶ Spec (.of R)}
  (b : Over.mk t ⟶ U) (s : Fin n → (relativeFppfSheaf f).obj.obj (op (Over.mk t)))

include hL ha hc hd in
/-- Independent geometric classes construct one translation on the full refined split fiber. -/
theorem exists_constructed_disjoint_geometric_translation :
    ∃ (d : ℕ) (W D : Over (Spec (.of R))) (q : W ⟶ U) (z : Over.mk t ⟶ W)
      (h : D ⟶ E) (r : D ⟶ W) (a' : Fin n → (W ⟶ D))
      (c : (relativeFppfSheaf f).obj.obj (op D)),
      IsAffine W.left ∧ Etale q.left ∧ z ≫ q = b ∧
      IsPullback h.left r.left p.left q.left ∧
      (∀ i, a' i ≫ r = 𝟙 W) ∧ (∀ i, a' i ≫ h = q ≫ a i) ∧
      (∀ i, s i * (relativeFppfSheaf f).obj.map (z ≫ a' i).op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t))) ∧
      ∀ w : Over.mk t ⟶ D, w ≫ r = z → ∃ i, w = z ≫ a' i ∧
        s i * (relativeFppfSheaf f).obj.map w.op c ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  obtain ⟨d, V, c, v, hV, he, hv⟩ :=
    exists_finite_geometric_etale_translations f hL t s
  let W : Over (Spec (.of R)) := Over.mk (pullback.snd V.hom U.hom ≫ U.hom)
  let q : W ⟶ U := Over.homMk (pullback.snd V.hom U.hom)
  let k : W ⟶ V := Over.homMk (pullback.fst V.hom U.hom) pullback.condition
  let z₀ := pullback.lift v.left b.left (v.w.trans b.w.symm)
  let z : Over.mk t ⟶ W := Over.homMk z₀ (by
    change z₀ ≫ pullback.snd V.hom U.hom ≫ U.hom = t
    rw [← Category.assoc, pullback.lift_snd]
    exact b.w)
  have hzq : z ≫ q = b := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
  have hzk : z ≫ k = v := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  let D : Over (Spec (.of R)) := Over.mk (pullback.snd p.left q.left ≫ W.hom)
  let r : D ⟶ W := Over.homMk (pullback.snd p.left q.left)
  let h : D ⟶ E := Over.homMk (pullback.fst p.left q.left) (by
    rw [← p.w, ← Category.assoc, pullback.condition, Category.assoc, q.w]
    rfl)
  have hasec (i : Fin n) : (a i).left ≫ p.left = 𝟙 U.left :=
    congrArg Over.Hom.left (ha i)
  let a₀ (i : Fin n) : W.left ⟶ pullback p.left q.left :=
    pullback.lift (q.left ≫ (a i).left) (𝟙 W.left) (by
      rw [Category.assoc, hasec, Category.comp_id, Category.id_comp])
  have har (i : Fin n) : a₀ i ≫ r.left = 𝟙 W.left := pullback.lift_snd _ _ _
  have hah (i : Fin n) : a₀ i ≫ h.left = q.left ≫ (a i).left :=
    pullback.lift_fst _ _ _
  let a' (i : Fin n) : W ⟶ D := Over.homMk (a₀ i) (by
    change a₀ i ≫ r.left ≫ W.hom = W.hom
    rw [← Category.assoc, har, Category.id_comp])
  have H : IsPullback h.left r.left p.left q.left := IsPullback.of_hasPullback _ _
  have ha' (i : Fin n) : a' i ≫ r = 𝟙 W := Over.OverMorphism.ext (har i)
  let _ (i : Fin n) : IsOpenImmersion (a' i).left :=
    DisjointSectionCoverCartesian.isOpenImmersion H (fun i ↦ (a i).left) a₀
      (fun i ↦ congrArg Over.Hom.left (ha i)) har hah i
  have hc' := DisjointSectionCoverCartesian.covers H (fun i ↦ (a i).left) a₀
    (fun i ↦ congrArg Over.Hom.left (ha i)) har hah hc
  have hd' := DisjointSectionCoverCartesian.disjoint (fun i ↦ (a i).left) a₀ hah hd
  have hm (i : Fin n) : s i * (relativeFppfSheaf f).obj.map z.op
      ((relativeFppfSheaf f).obj.map k.op (c i)) ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hzk]
    exact hv i
  obtain ⟨c', hres, _⟩ := disjointSection_existsUnique f r a' hc' hd'
    (fun i ↦ (relativeFppfSheaf f).obj.map k.op (c i))
  have hm' (i : Fin n) : s i * (relativeFppfSheaf f).obj.map (z ≫ a' i).op c' ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hres]
    exact hm i
  refine ⟨d, W, D, q, z, h, r, a', c',
    inferInstanceAs (IsAffine (pullback V.hom U.hom)),
    inferInstanceAs (Etale (pullback.snd V.hom U.hom)), hzq, H, ha',
    fun i ↦ Over.OverMorphism.ext (hah i), hm', fun w hw ↦ ?_⟩
  obtain ⟨i, hi⟩ := SectionCoverGeometricMorphisms.exists_sheet r.left
    (fun i ↦ (a' i).left) har hc' z.left w.left (congrArg Over.Hom.left hw)
  have hw' : w = z ≫ a' i := Over.OverMorphism.ext hi
  refine ⟨i, hw', ?_⟩
  rw [hw']
  exact hm' i

end FLT.Mazur.HilbertChart
