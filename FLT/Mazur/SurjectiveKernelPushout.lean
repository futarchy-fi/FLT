/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Intersections from sums of kernels

A surjective common restriction whose kernel is the sum of two component
kernels is their pushout in commutative rings. This proves the full universal
property without unfolding a tensor product presentation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.SurjectiveKernelPushout
universe u
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  (f : A →+* B) (g : A →+* C) (l : B →+* D) (r : C →+* D)
  (hf : Function.Surjective f) (hg : Function.Surjective g)
  (hk : Function.Surjective (l.comp f)) (w : l.comp f = r.comp g)
  (hker : RingHom.ker (l.comp f) = RingHom.ker f ⊔ RingHom.ker g)

include hker in
/-- Every compatible pair kills the sum of the original component kernels. -/
theorem ker_le (s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom g)) :
    RingHom.ker (l.comp f) ≤ RingHom.ker (s.inl.hom.comp f) := by
  rw [hker]
  refine sup_le ?_ ?_
  · intro a ha
    change s.inl.hom (f a) = 0
    rw [show f a = 0 from ha, map_zero]
  · intro a ha
    have hw := congrArg (fun m => m.hom a) s.condition
    change s.inl.hom (f a) = s.inr.hom (g a) at hw
    change s.inl.hom (f a) = 0
    rw [hw, show g a = 0 from ha, map_zero]

/-- The descended map on the entire proposed intersection ring. -/
def desc (s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom g)) :
    CommRingCat.of D ⟶ s.pt :=
  CommRingCat.ofHom ((l.comp f).liftOfSurjective hk
    ⟨s.inl.hom.comp f, ker_le f g l hker s⟩)

include hf in
/-- Descent keeps every function restricted from the first component. -/
theorem inl_desc (s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom g)) :
    CommRingCat.ofHom l ≫ desc f g l hk hker s = s.inl := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact (l.comp f).liftOfSurjective_comp_apply hk
    ⟨s.inl.hom.comp f, ker_le f g l hker s⟩ a

include hg w in
/-- Descent keeps every function restricted from the second component. -/
theorem inr_desc (s : PushoutCocone (CommRingCat.ofHom f) (CommRingCat.ofHom g)) :
    CommRingCat.ofHom r ≫ desc f g l hk hker s = s.inr := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  obtain ⟨a, rfl⟩ := hg c
  have hw := DFunLike.congr_fun w a
  change l (f a) = r (g a) at hw
  change (desc f g l hk hker s).hom (r (g a)) = s.inr.hom (g a)
  rw [← hw]
  exact ((l.comp f).liftOfSurjective_comp_apply hk
    ⟨s.inl.hom.comp f, ker_le f g l hker s⟩ a).trans
    (congrArg (fun m => m.hom a) s.condition)

include hf hg hk w hker in
/-- A surjective common restriction with the exact summed kernel is the full pushout. -/
theorem isPushout : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
    (CommRingCat.ofHom l) (CommRingCat.ofHom r) := by
  have hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom l =
      CommRingCat.ofHom g ≫ CommRingCat.ofHom r := CommRingCat.hom_ext w
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw)
    (PushoutCocone.IsColimit.mk _ (desc f g l hk hker)
      (inl_desc f g l hf hk hker) (inr_desc f g l r hg hk w hker) ?_)
  intro s m hm _
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro d
  obtain ⟨a, rfl⟩ := hk d
  exact (congrArg (fun t => t.hom (f a)) hm).trans
    ((l.comp f).liftOfSurjective_comp_apply hk
    ⟨s.inl.hom.comp f, ker_le f g l hker s⟩ a).symm

end FLT.Mazur.SurjectiveKernelPushout
