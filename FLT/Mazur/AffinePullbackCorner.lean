/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Comparing affine pullback corners

A map between two affine pullback corners that retains both projections is
bijective. Conversely a bijective corner map transfers the pullback property.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {S R B C D E : Type u}
  [CommRing S] [CommRing R] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
  [Algebra S R] [Algebra S B] [Algebra S C] [Algebra S D] [Algebra S E]
  (f : R →ₐ[S] B) (g : R →ₐ[S] C)
  (i : B →ₐ[S] D) (j : C →ₐ[S] D)
  (i' : B →ₐ[S] E) (j' : C →ₐ[S] E) (q : D →ₐ[S] E)
  (hi : q.comp i = i') (hj : q.comp j = j')

include hi hj

/-- A comparison retaining two pullback projections is necessarily bijective. -/
theorem affinePullback_corner_bijective
    (hp : IsPullback (Spec.map (CommRingCat.ofHom i.toRingHom))
      (Spec.map (CommRingCat.ofHom j.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)))
    (hp' : IsPullback (Spec.map (CommRingCat.ofHom i'.toRingHom))
      (Spec.map (CommRingCat.ofHom j'.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom))) : Function.Bijective q := by
  have ht := (hp.of_map_of_faithful Scheme.Spec).unop.flip
  have ht' := (hp'.of_map_of_faithful Scheme.Spec).unop.flip
  let e := ht.isoIsPushout _ _ ht'
  have he : CommRingCat.ofHom q.toRingHom = e.hom := by
    apply ht.hom_ext
    · rw [ht.inl_isoIsPushout_hom]
      exact congrArg (fun a : B →ₐ[S] E ↦ CommRingCat.ofHom a.toRingHom) hi
    · rw [ht.inr_isoIsPushout_hom]
      exact congrArg (fun a : C →ₐ[S] E ↦ CommRingCat.ofHom a.toRingHom) hj
  change Function.Bijective (CommRingCat.ofHom q.toRingHom)
  rw [he]
  exact ConcreteCategory.bijective_of_isIso _

/-- A bijective comparison retaining both projections transfers cartesianness. -/
theorem affinePullback_of_corner_bijective
    (hp : IsPullback (Spec.map (CommRingCat.ofHom i.toRingHom))
      (Spec.map (CommRingCat.ofHom j.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom))) (hq : Function.Bijective q) :
    IsPullback (Spec.map (CommRingCat.ofHom i'.toRingHom))
      (Spec.map (CommRingCat.ofHom j'.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
  have ht := (hp.of_map_of_faithful Scheme.Spec).unop.flip
  apply isPullback_SpecMap_of_isPushout
  apply ht.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (AlgEquiv.ofBijective q hq).toRingEquiv.toCommRingCatIso (by simp) (by simp)
  · exact congrArg (fun a : B →ₐ[S] E ↦ CommRingCat.ofHom a.toRingHom) hi
  · exact congrArg (fun a : C →ₐ[S] E ↦ CommRingCat.ofHom a.toRingHom) hj

end FLT.Mazur.Approximation
