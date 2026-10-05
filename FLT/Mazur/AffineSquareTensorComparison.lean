/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The tensor comparison of an affine square

A commutative square of algebra maps gives a canonical map from its tensor
pushout. Its values on pure tensors retain both arrows into the corner.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {S R B C D : Type u}
  [CommRing S] [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra S R] [Algebra S B] [Algebra S C] [Algebra S D]
  (f : R →ₐ[S] B) (g : R →ₐ[S] C)
  (i : B →ₐ[S] D) (j : C →ₐ[S] D) (h : i.comp f = j.comp g)

/-- The comparison from the tensor pushout to a commutative square's corner. -/
def affineSquareTensorComparison :
    letI := f.toRingHom.toAlgebra
    letI := g.toRingHom.toAlgebra
    B ⊗[R] C →ₐ[S] D := by
  letI := f.toRingHom.toAlgebra
  letI := g.toRingHom.toAlgebra
  letI := (i.comp f).toRingHom.toAlgebra
  let iR : B →ₐ[R] D :=
    { i.toRingHom with commutes' := fun _ ↦ rfl }
  let jR : C →ₐ[R] D :=
    { j.toRingHom with commutes' := fun r ↦ (AlgHom.congr_fun h r).symm }
  exact (Algebra.TensorProduct.lift iR jR (fun _ _ ↦ Commute.all _ _)).restrictScalars S

/-- The comparison is the product of the two given corner maps. -/
@[simp]
theorem affineSquareTensorComparison_tmul (b : B) (c : C) :
    letI := f.toRingHom.toAlgebra
    letI := g.toRingHom.toAlgebra
    affineSquareTensorComparison f g i j h (b ⊗ₜ c) = i b * j c := rfl

/-- The left tensor inclusion recovers the square's left corner map. -/
theorem affineSquareTensorComparison_left (b : B) :
    letI := f.toRingHom.toAlgebra
    letI := g.toRingHom.toAlgebra
    affineSquareTensorComparison f g i j h (b ⊗ₜ 1) = i b := by
  simp

/-- The right tensor inclusion recovers the square's right corner map. -/
theorem affineSquareTensorComparison_right (c : C) :
    letI := f.toRingHom.toAlgebra
    letI := g.toRingHom.toAlgebra
    affineSquareTensorComparison f g i j h (1 ⊗ₜ c) = j c := by
  simp

/-- Bijectivity of the canonical comparison makes the actual affine square cartesian. -/
theorem affineSquare_isPullback_of_tensorComparison_bijective
    (hb : Function.Bijective (affineSquareTensorComparison f g i j h)) :
    IsPullback (Spec.map (CommRingCat.ofHom i.toRingHom))
      (Spec.map (CommRingCat.ofHom j.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
  let := f.toRingHom.toAlgebra
  let := g.toRingHom.toAlgebra
  let e := AlgEquiv.ofBijective (affineSquareTensorComparison f g i j h) hb
  apply isPullback_SpecMap_of_isPushout
  apply (CommRingCat.isPushout_tensorProduct R B C).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    (by rfl) (by rfl)
  · ext b
    exact affineSquareTensorComparison_left f g i j h b
  · ext c
    exact affineSquareTensorComparison_right f g i j h c

/-- A cartesian affine square has a bijective canonical tensor comparison. -/
theorem affineSquare_tensorComparison_bijective_of_isPullback
    (hp : IsPullback (Spec.map (CommRingCat.ofHom i.toRingHom))
      (Spec.map (CommRingCat.ofHom j.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom))) :
    Function.Bijective (affineSquareTensorComparison f g i j h) := by
  let := f.toRingHom.toAlgebra
  let := g.toRingHom.toAlgebra
  have hq := (hp.of_map_of_faithful Scheme.Spec).unop.flip
  have ht := CommRingCat.isPushout_tensorProduct R B C
  let e := ht.isoIsPushout _ _ hq
  have he : CommRingCat.ofHom (affineSquareTensorComparison f g i j h).toRingHom =
      e.hom := by
    apply ht.hom_ext
    · rw [ht.inl_isoIsPushout_hom]
      ext b
      exact affineSquareTensorComparison_left f g i j h b
    · rw [ht.inr_isoIsPushout_hom]
      ext c
      exact affineSquareTensorComparison_right f g i j h c
  change Function.Bijective (CommRingCat.ofHom
    (affineSquareTensorComparison f g i j h).toRingHom)
  rw [he]
  exact ConcreteCategory.bijective_of_isIso _

end FLT.Mazur.Approximation
