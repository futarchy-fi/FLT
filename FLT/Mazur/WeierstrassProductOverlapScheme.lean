/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProductOverlap
public import FLT.Mazur.ProjectiveProductChartOverlaps

/-!
# Open immersions for input-product chart changes

The tensor restrictions are open immersions: under the tensor-spectrum
identification they are the fiber product of two principal open immersions.
The explicit transition isomorphism gives the second open immersion as well.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassIntegralChart

open FLT.Mazur.ProjectiveSpace

universe u

variable {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Tensoring two open affine maps over the same base again gives an open immersion. -/
theorem tensorSpecMap_isOpenImmersion (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom))] :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map f g).toRingHom)) := by
  let m := pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (Spec.map (CommRingCat.ofHom (algebraMap R D)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (Spec.map (CommRingCat.ofHom f.toRingHom))
    (Spec.map (CommRingCat.ofHom g.toRingHom)) (𝟙 _)
    (by simpa only [Category.comp_id] using (specAlgHom_base R f).symm)
    (by simpa only [Category.comp_id] using (specAlgHom_base R g).symm)
  have he : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map f g).toRingHom) =
      (pullbackSpecIso R C D).inv ≫ m ≫ (pullbackSpecIso R A B).hom := by
    apply (tensorSpecIsPullback R A B).hom_ext
    · simp only [Category.assoc, tensorSpecMap_fst, tensorSpecFst,
        pullbackSpecIso_hom_fst, m, pullback.map, pullback.lift_fst]
      rw [← Category.assoc, pullbackSpecIso_inv_fst]
    · simp only [Category.assoc, tensorSpecSnd,
        AlgHom.toRingHom_eq_coe, pullbackSpecIso_hom_snd R A B, m, pullback.map, pullback.lift_snd]
      rw [← Category.assoc, pullbackSpecIso_inv_snd]
      exact tensorSpecMap_snd R f g
  rw [he]
  infer_instance

variable (W : WeierstrassCurve R) (j k j' k' : Fin 3)

/-- The simultaneous overlap is open in the first input-chart product. -/
instance productOverlapRestriction_isOpenImmersion :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (productOverlapRestriction W j k j' k').toRingHom)) := by
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (overlapRestriction W j j').toRingHom)) :=
    IsOpenImmersion.of_isLocalization (coord W j j')
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (overlapRestriction W k k').toRingHom)) :=
    IsOpenImmersion.of_isLocalization (coord W k k')
  exact tensorSpecMap_isOpenImmersion _ _

/-- The normalized restriction is open in the other input-chart product too. -/
instance productOverlapOther_isOpenImmersion :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (productOverlapOther W j k j' k').toRingHom)) := by
  rw [← productOverlapEquiv_restriction]
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    ((productOverlapEquiv W j k j' k').toAlgHom.toRingHom.comp
      (productOverlapRestriction W j' k' j k).toRingHom)))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsIso (CommRingCat.ofHom (productOverlapEquiv W j k j' k').toAlgHom.toRingHom) :=
    show IsIso (productOverlapEquiv W j k j' k').toRingEquiv.toCommRingCatIso.hom
      from inferInstance
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
