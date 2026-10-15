/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothGeometricOpenEtaleLift
public import FLT.Mazur.UnpointedAcyclicDegreeOpen

/-!
# Original étale translations of arbitrary geometric Picard classes

A nonempty acyclic degree open in a smooth translation fiber gives an
original affine étale translation. The prescribed geometric Picard class
is unchanged, even though the smooth translation coordinate can change.
Only the constructed lift is asserted acyclic, not all its conjugates.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {K : Type} [Field K] [IsSepClosed K] {t : Spec (.of K) ⟶ Spec (.of R)}
  (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) (v : Over.mk t ⟶ V)

/-- A smooth acyclic translation yields an original affine étale translation of the same class. -/
theorem exists_etale_translation_of_geometric_acyclicity
    (hv : s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t))) :
    ∃ (E : Over (Spec (.of R))) (r : E ⟶ V) (z : Over.mk t ⟶ E),
      IsAffine E.left ∧ Etale E.hom ∧
      s * (relativeFppfSheaf f).obj.map z.op
        ((relativeFppfSheaf f).obj.map r.op c) ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  let Y : Over (Spec (.of R)) := Over.mk (pullback.fst V.hom t ≫ V.hom)
  let a : Y ⟶ V := Over.homMk (pullback.fst V.hom t)
  let b : Y ⟶ Over.mk t := Over.homMk (pullback.snd V.hom t) pullback.condition.symm
  let C := (relativeFppfSheaf f).obj.map b.op s *
    (relativeFppfSheaf f).obj.map a.op c
  let D := unpointedAcyclicDegreeTest f Y C d
  let j := unpointedAcyclicDegreeArrow f Y C d
  let w : Over.mk t ⟶ Y := Over.homMk
    (pullback.lift v.left (𝟙 _) (by rw [Category.id_comp]; exact v.w)) (by
      change _ ≫ (pullback.fst V.hom t ≫ V.hom) = t
      rw [← Category.assoc, pullback.lift_fst]
      exact v.w)
  have hwa : w ≫ a = v := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have hwb : w ≫ b = 𝟙 _ := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
  have hw : (relativeFppfSheaf f).obj.map w.op C ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
    dsimp only [C]
    rw [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hwb,
      op_id, (relativeFppfSheaf f).obj.map_id]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hwa]
    exact hv
  obtain ⟨l, _, _⟩ := (unpointedAcyclicDegreeOpen_represents f Y C d w).mp hw
  have hn : Nonempty D.left := ⟨l.left (default : Spec (.of K))⟩
  obtain ⟨E, e, r, z, u, hE, he, hr, hz, hu, hur⟩ :=
    SmoothGeometricOpenEtaleLift.exists_lift V.hom t a.left b.left
      (IsPullback.of_hasPullback V.hom t) j.left hn
  let E' : Over (Spec (.of R)) := Over.mk e
  let r' : E' ⟶ V := Over.homMk r hr
  let z' : Over.mk t ⟶ E' := Over.homMk z hz
  let u' : Over.mk t ⟶ D := Over.homMk u (by
    change u ≫ D.hom = t
    rw [← j.w, ← b.w, ← Category.assoc, ← Category.assoc, Category.assoc u j.left, hu,
      Category.id_comp]
    rfl)
  have hub : u' ≫ j ≫ b = 𝟙 _ := Over.OverMorphism.ext hu
  have hua : u' ≫ j ≫ a = z' ≫ r' := Over.OverMorphism.ext hur.symm
  have h := (acyclicDegreePicardSubfunctor f d).map u'.op
    (unpointedAcyclicDegreeArrow_mem f Y C d)
  change (relativeFppfSheaf f).obj.map u'.op
    ((relativeFppfSheaf f).obj.map j.op C) ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) at h
  refine ⟨E', r', z', hE, he, ?_⟩
  have hcomp {A B C : Over (Spec (.of R))} (a : A ⟶ B) (b : B ⟶ C)
      (x : (relativeFppfSheaf f).obj.obj (op C)) :
      (relativeFppfSheaf f).obj.map a.op ((relativeFppfSheaf f).obj.map b.op x) =
        (relativeFppfSheaf f).obj.map (a ≫ b).op x := by
    rw [op_comp, Functor.map_comp]
    rfl
  dsimp only [C] at h
  rw [map_mul, map_mul, hcomp, hcomp, hcomp, hcomp, Category.assoc, hub,
    Category.assoc, hua, op_id, (relativeFppfSheaf f).obj.map_id] at h
  rw [hcomp]
  exact h

end FLT.Mazur.HilbertChart
