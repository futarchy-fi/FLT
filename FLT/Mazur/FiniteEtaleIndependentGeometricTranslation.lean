/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstructedDisjointGeometricTranslation
public import FLT.Mazur.FiniteEtaleGeometricDisjointCover

/-!
# Independent geometric translations on a constructed finite étale splitting

An arbitrary family of geometric Picard classes, indexed by whole original
source morphisms, acquires one original translation on a constructed base
change of a finite étale source. The result recovers each prescribed class
through the actual original-source map. It covers every lift over the retained
geometric splitting-base map, without a global extension of those classes.
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
  (p : E ⟶ U) [IsFinite p.left] [Etale p.left]
  {K : Type} [Field K] [IsAlgClosed K] {t : Spec (.of K) ⟶ Spec (.of R)}
  (b : Over.mk t ⟶ U)
  (s : (Over.mk t ⟶ E) → (relativeFppfSheaf f).obj.obj (op (Over.mk t)))

include hL in
/-- Independent original geometric classes acquire one translation on the full refined source. -/
theorem exists_finiteEtale_independent_geometric_translation :
    ∃ (d : ℕ) (W D : Over (Spec (.of R))) (q : W ⟶ U) (z : Over.mk t ⟶ W)
      (h : D ⟶ E) (r : D ⟶ W) (c : (relativeFppfSheaf f).obj.obj (op D)),
      IsAffine W.left ∧ Etale q.left ∧ z ≫ q = b ∧
      IsPullback h.left r.left p.left q.left ∧
      (∀ v : Over.mk t ⟶ E, v ≫ p = b →
        ∃! w : Over.mk t ⟶ D, w ≫ h = v ∧ w ≫ r = z) ∧
      ∀ w : Over.mk t ⟶ D, w ≫ r = z →
        s (w ≫ h) * (relativeFppfSheaf f).obj.map w.op c ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  obtain ⟨n, U₀, E₀, q₀, z₀, h₀, r₀, a₀, hU, hq, _, hz, H, _, _, ha, hi, hc, hd⟩ :=
    FiniteEtaleGeometricDisjointCover.exists_cover p.left b.left
  let U' : Over (Spec (.of R)) := Over.mk (q₀ ≫ U.hom)
  let q' : U' ⟶ U := Over.homMk q₀
  let z' : Over.mk t ⟶ U' := Over.homMk z₀ (by
    change z₀ ≫ q₀ ≫ U.hom = t
    rw [← Category.assoc, hz]
    exact b.w)
  let E' : Over (Spec (.of R)) := Over.mk (r₀ ≫ U'.hom)
  let r' : E' ⟶ U' := Over.homMk r₀
  let h' : E' ⟶ E := Over.homMk h₀ (by
    rw [← p.w, ← Category.assoc, H.w, Category.assoc]
    rfl)
  let a' (i : Fin n) : U' ⟶ E' := Over.homMk (a₀ i) (by
    change a₀ i ≫ r₀ ≫ U'.hom = U'.hom
    rw [← Category.assoc, ha, Category.id_comp])
  let _ : IsAffine U'.left := hU
  let _ (i : Fin n) : IsOpenImmersion (a' i).left := hi i
  have ha' (i : Fin n) : a' i ≫ r' = 𝟙 U' := Over.OverMorphism.ext (ha i)
  obtain ⟨d, W, D, q, z, h, r, a, c, hW, he, hz', H', _, hah, _, hm⟩ :=
    exists_constructed_disjoint_geometric_translation f hL r' a' ha' hc hd z'
      (fun i ↦ s (z' ≫ a' i ≫ h'))
  have hbase : z' ≫ q' = b := Over.OverMorphism.ext hz
  have hbase' : z ≫ (q ≫ q') = b := by rw [← Category.assoc, hz', hbase]
  have Htotal : IsPullback (h ≫ h').left r.left p.left (q ≫ q').left := H'.paste_horiz H
  refine ⟨d, W, D, q ≫ q', z, h ≫ h', r, c, hW,
    inferInstanceAs (Etale (q.left ≫ q₀)), hbase', Htotal, ?_, fun w hw ↦ ?_⟩
  · intro v hv
    have hvz : v.left ≫ p.left = z.left ≫ (q ≫ q').left :=
      congrArg Over.Hom.left (hv.trans hbase'.symm)
    let w₀ := Htotal.lift v.left z.left hvz
    have hwr : w₀ ≫ r.left = z.left := Htotal.lift_snd _ _ _
    have hwh : w₀ ≫ (h ≫ h').left = v.left := Htotal.lift_fst _ _ _
    let w : Over.mk t ⟶ D := Over.homMk w₀ (by
      rw [← r.w, ← Category.assoc, hwr]
      exact z.w)
    refine ⟨w, ⟨Over.OverMorphism.ext hwh, Over.OverMorphism.ext hwr⟩, fun w' hw' ↦ ?_⟩
    apply Over.OverMorphism.ext
    apply Htotal.hom_ext
    · exact (congrArg Over.Hom.left hw'.1).trans hwh.symm
    · exact (congrArg Over.Hom.left hw'.2).trans hwr.symm
  · obtain ⟨i, hi, hm⟩ := hm w hw
    have hwmap : w ≫ h = z' ≫ a' i := by
      rw [hi, Category.assoc, hah, ← Category.assoc, hz']
    have heq : w ≫ h ≫ h' = z' ≫ a' i ≫ h' := by
      rw [← Category.assoc, hwmap, Category.assoc]
    rw [heq]
    exact hm

end FLT.Mazur.HilbertChart
