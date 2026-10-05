/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Identifying affine cartesian squares

Compatible algebra equivalences identify the pullback property while
retaining all four specified arrows.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- Compatible algebra equivalences identify cartesian affine squares. -/
theorem affineSquare_isPullback_iff_of_equivs {S R B C D R' B' C' D' : Type u}
    [CommRing S] [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [CommRing R'] [CommRing B'] [CommRing C'] [CommRing D']
    [Algebra S R] [Algebra S B] [Algebra S C] [Algebra S D]
    [Algebra S R'] [Algebra S B'] [Algebra S C'] [Algebra S D']
    (f : R →ₐ[S] B) (g : R →ₐ[S] C) (i : B →ₐ[S] D) (j : C →ₐ[S] D)
    (f' : R' →ₐ[S] B') (g' : R' →ₐ[S] C')
    (i' : B' →ₐ[S] D') (j' : C' →ₐ[S] D')
    (eR : R ≃ₐ[S] R') (eB : B ≃ₐ[S] B') (eC : C ≃ₐ[S] C') (eD : D ≃ₐ[S] D')
    (hf : eB.toAlgHom.comp f = f'.comp eR.toAlgHom)
    (hg : eC.toAlgHom.comp g = g'.comp eR.toAlgHom)
    (hi : eD.toAlgHom.comp i = i'.comp eB.toAlgHom)
    (hj : eD.toAlgHom.comp j = j'.comp eC.toAlgHom) :
    IsPullback (Spec.map (CommRingCat.ofHom i.toRingHom))
      (Spec.map (CommRingCat.ofHom j.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) ↔
    IsPullback (Spec.map (CommRingCat.ofHom i'.toRingHom))
      (Spec.map (CommRingCat.ofHom j'.toRingHom))
      (Spec.map (CommRingCat.ofHom f'.toRingHom))
      (Spec.map (CommRingCat.ofHom g'.toRingHom)) := by
  have hf' := congrArg (fun a : R →ₐ[S] B' ↦ CommRingCat.ofHom a.toRingHom) hf
  have hg' := congrArg (fun a : R →ₐ[S] C' ↦ CommRingCat.ofHom a.toRingHom) hg
  have hi' := congrArg (fun a : B →ₐ[S] D' ↦ CommRingCat.ofHom a.toRingHom) hi
  have hj' := congrArg (fun a : C →ₐ[S] D' ↦ CommRingCat.ofHom a.toRingHom) hj
  constructor
  · intro hp
    apply isPullback_SpecMap_of_isPushout
    exact ((hp.of_map_of_faithful Scheme.Spec).unop.flip).of_iso
      eR.toRingEquiv.toCommRingCatIso eB.toRingEquiv.toCommRingCatIso
      eC.toRingEquiv.toCommRingCatIso eD.toRingEquiv.toCommRingCatIso hf' hg' hi' hj'
  · intro hp
    apply isPullback_SpecMap_of_isPushout
    exact ((hp.of_map_of_faithful Scheme.Spec).unop.flip).of_iso'
      eR.toRingEquiv.toCommRingCatIso eB.toRingEquiv.toCommRingCatIso
      eC.toRingEquiv.toCommRingCatIso eD.toRingEquiv.toCommRingCatIso
      hf'.symm hg'.symm hi'.symm hj'.symm

end FLT.Mazur.Approximation
