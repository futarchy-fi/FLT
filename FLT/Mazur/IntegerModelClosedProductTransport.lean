/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorIntegerModelTransport
public import FLT.Mazur.IntegerModelPropertyTransport
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed overlap products persist under enlargement

Closedness of the product of two fixed restriction maps survives a common
coefficient extension, with no flatness requirement on that extension.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- Transport retains closedness of the actual overlap map into the chart product. -/
theorem integerModelTransportHom_product_closedImmersion {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] {n m r t k l : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (T : Algebra.Presentation A D (Fin k) (Fin l))
    {R S : Subalgebra ℤ A} [P.HasCoeffs R] [Q.HasCoeffs R] [T.HasCoeffs R]
    [P.HasCoeffs S] [Q.HasCoeffs S] [T.HasCoeffs S] (h : R ≤ S)
    (f : P.ModelOfHasCoeffs R →ₐ[R] T.ModelOfHasCoeffs R)
    (g : Q.ModelOfHasCoeffs R →ₐ[R] T.ModelOfHasCoeffs R)
    (hc : IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (Algebra.TensorProduct.productMap f g).toRingHom))) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.productMap (integerModelTransportHom P T h f)
        (integerModelTransportHom Q T h g)).toRingHom)) := by
  let := integerModel_hasCoeffs_mono (tensorIntegerPresentation P Q R) h
  have h₀ : IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (tensorIntegerModelMap P Q T R f g).toRingHom)) := by
    change IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (tensorIntegerPresentationEquiv P Q R).toRingHom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.productMap f g).toRingHom))
    rw [Spec.map_comp]
    let : IsIso (CommRingCat.ofHom (tensorIntegerPresentationEquiv P Q R).toRingHom) :=
      (tensorIntegerPresentationEquiv P Q R).toRingEquiv.toCommRingCatIso.isIso_hom
    exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mpr hc
  have ht := integerModelTransportHom_property (tensorIntegerPresentation P Q R) T h
    (tensorIntegerModelMap P Q T R f g) @IsClosedImmersion h₀
  rw [tensorIntegerModelMap_transport] at ht
  change IsClosedImmersion (Spec.map
    (CommRingCat.ofHom (tensorIntegerPresentationEquivAt P Q h).toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.productMap
        (integerModelTransportHom P T h f) (integerModelTransportHom Q T h g)).toRingHom)) at ht
  rw [Spec.map_comp] at ht
  let : IsIso (CommRingCat.ofHom (tensorIntegerPresentationEquivAt P Q h).toRingHom) :=
    (tensorIntegerPresentationEquivAt P Q h).toRingEquiv.toCommRingCatIso.isIso_hom
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mp ht

end FLT.Mazur.Approximation
