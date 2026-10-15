/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalSmoothFiberAllLifts
public import FLT.Mazur.UnpointedAcyclicDegreeOpen

/-!
# All independent translations over transcendental coefficient fields

A nonempty actual acyclic open yields one original affine étale translation
valid for every independent K-lift and the same arbitrary input class.
No finite orbit or descent of that class is required. The original smooth
translation parameter is geometrically integral.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R k L K : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [Field k] [Field L] [Field K] [Algebra k L] [Algebra L K] [Algebra k K]
  [IsScalarTower k L K] [IsAlgClosed L] [Algebra.IsAlgebraic k L]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  (t : Spec (.of k) ⟶ Spec (.of R)) [IsPreimmersion t]
variable (d : ℕ) {V Y : Over (Spec (.of R))} [Smooth V.hom] [GeometricallyIntegral V.hom]
  (a : Y ⟶ V) (b : Y ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t))
  (H : IsPullback a.left b.left V.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (s : (relativeFppfSheaf f).obj.obj
    (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t))))
include L H

/-- The same arbitrary class is acyclic at every independent original lift of the new test. -/
theorem exists_transcendental_all_independent_acyclic_translation
    (hne : ((unpointedAcyclicDegreeArrow f Y
          ((relativeFppfSheaf f).obj.map b.op s *
            (relativeFppfSheaf f).obj.map a.op c) d).left.opensRange : Set Y.left).Nonempty) :
    ∃ (E : Over (Spec (.of R))) (r : E ⟶ V)
      (_z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ E),
      IsAffine E.left ∧ Etale E.hom ∧
      ∀ w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ E,
        s * (relativeFppfSheaf f).obj.map w.op
          ((relativeFppfSheaf f).obj.map r.op c) ∈
            (acyclicDegreePicardSubfunctor f d).obj
              (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t))) := by
  let C := (relativeFppfSheaf f).obj.map b.op s * (relativeFppfSheaf f).obj.map a.op c
  let D := unpointedAcyclicDegreeTest f Y C d
  let j := unpointedAcyclicDegreeArrow f Y C d
  let U := j.left.opensRange
  obtain ⟨E, e, r, z, hE, he, hr, hz, hall⟩ :=
    OriginalSmoothFiberAllLifts.exists_all_lifts (L := L) V.hom t a.left b.left H
      (fun _ : Unit ↦ U) (fun _ ↦ hne)
  let E' : Over (Spec (.of R)) := Over.mk e
  let r' : E' ⟶ V := Over.homMk r hr
  let z' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ E' := Over.homMk z hz
  refine ⟨E', r', z', hE, he, fun w ↦ ?_⟩
  obtain ⟨u, hub, hua, hum⟩ := hall w.left w.w
  have hu : Set.range u ⊆ Set.range (j).left := hum ()
  let v := IsOpenImmersion.lift (j).left u hu
  have hv : v ≫ (j).left = u := IsOpenImmersion.lift_fac _ _ _
  have hvb : v ≫ (j).left ≫ b.left = 𝟙 _ := by
    rw [← Category.assoc, hv]
    exact hub
  have hva : v ≫ (j).left ≫ a.left = w.left ≫ r := by
    rw [← Category.assoc, hv]
    exact hua.symm
  let v' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ D := Over.homMk v (by
    rw [← (j).w, ← b.w, ← Category.assoc, ← Category.assoc,
      Category.assoc v (j).left, hvb]
    exact Category.id_comp _)
  have hvb' : v' ≫ j ≫ b = 𝟙 _ := Over.OverMorphism.ext hvb
  have hva' : v' ≫ j ≫ a = w ≫ r' := Over.OverMorphism.ext hva
  have h := (acyclicDegreePicardSubfunctor f d).map v'.op
    (unpointedAcyclicDegreeArrow_mem f Y C d)
  change (relativeFppfSheaf f).obj.map v'.op
    ((relativeFppfSheaf f).obj.map (j).op C) ∈
      (acyclicDegreePicardSubfunctor f d).obj
        (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t))) at h
  have hcomp {A B Z : Over (Spec (.of R))} (p : A ⟶ B) (q : B ⟶ Z)
      (x : (relativeFppfSheaf f).obj.obj (op Z)) :
      (relativeFppfSheaf f).obj.map p.op ((relativeFppfSheaf f).obj.map q.op x) =
        (relativeFppfSheaf f).obj.map (p ≫ q).op x := by
    rw [op_comp, Functor.map_comp]
    rfl
  rw [map_mul, map_mul, hcomp, hcomp, hcomp, hcomp, Category.assoc, hvb',
    Category.assoc, hva', op_id, (relativeFppfSheaf f).obj.map_id] at h
  rw [hcomp]
  exact h

end FLT.Mazur.HilbertChart
