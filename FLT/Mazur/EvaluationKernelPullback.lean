/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Cartesian evaluation squares from exact ideal equality

If a map of algebras carries one evaluation ideal onto the other, its fiber
over the original section is exactly the original section of the source.
The universal property is proved directly, without expanding tensor products.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.EvaluationKernelPullback

universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  (f : A →ₐ[K] B) (a : A →ₐ[K] K) (b : B →ₐ[K] K)
  (h : b.comp f = a)
  (hk : Ideal.map f.toRingHom (RingHom.ker a.toRingHom) = RingHom.ker b.toRingHom)

include h hk
/-- Exact evaluation ideals give the full ring pushout square. -/
theorem isPushout : IsPushout (CommRingCat.ofHom f.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom)
    (𝟙 (CommRingCat.of K)) := by
  have hb : Function.Surjective b := fun x => ⟨algebraMap K B x, by simp⟩
  have hw : CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom b.toRingHom =
      CommRingCat.ofHom a.toRingHom ≫ 𝟙 (CommRingCat.of K) :=
    CommRingCat.hom_ext (congrArg AlgHom.toRingHom h)
  let c := PushoutCocone.mk _ _ hw
  have hl (s : PushoutCocone (CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom a.toRingHom)) : RingHom.ker b.toRingHom ≤ RingHom.ker s.inl.hom := by
    rw [← hk, Ideal.map_le_iff_le_comap]
    intro x hx
    have hs := congrArg (fun k => k.hom x) s.condition
    change s.inl.hom (f x) = s.inr.hom (a x) at hs
    change s.inl.hom (f x) = 0
    rw [hs, show a x = 0 from hx, map_zero]
  let d (s : PushoutCocone (CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom a.toRingHom)) : CommRingCat.of K ⟶ s.pt :=
    CommRingCat.ofHom (b.toRingHom.liftOfSurjective hb ⟨s.inl.hom, hl s⟩)
  have hd (s) (x : B) : (d s).hom (b x) = s.inl.hom x :=
    b.toRingHom.liftOfSurjective_comp_apply hb ⟨s.inl.hom, hl s⟩ x
  refine IsPushout.of_isColimit (c := c) (PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_)
  · intro s
    exact CommRingCat.hom_ext (RingHom.ext (hd s))
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    have hs := congrArg (fun k => k.hom (algebraMap K A x)) s.condition
    simpa using (hd s (algebraMap K B x)).trans (by simpa using hs)
  · intro s m hm _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hb x
    exact (congrArg (fun k => k.hom y) hm).trans (hd s y).symm

/-- The original source section is the full scheme fiber of the original target section. -/
theorem isPullback : IsPullback (Spec.map (CommRingCat.ofHom b.toRingHom))
    (𝟙 (Spec (.of K))) (Spec.map (CommRingCat.ofHom f.toRingHom))
    (Spec.map (CommRingCat.ofHom a.toRingHom)) := by
  simpa only [Spec.map_id] using
    isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout f a b h hk)

end FLT.Mazur.EvaluationKernelPullback
