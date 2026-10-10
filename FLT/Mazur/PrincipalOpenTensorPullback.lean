/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChartCommonBoundary

/-!
# Cartesian restriction squares for tensor principal opens

The actual localized tensor algebra is the entire inverse image of the
original principal open. The inverse transition preserves this square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (x : A) (y : B) (e : Localization.Away x ≃ₐ[R] Localization.Away y)

/-- Principal restriction in the tensor algebra is the full original base change. -/
theorem inclusion_isPullback :
    IsPullback (inclusion (R := R) S x) (projection S x) TensorOpenChart.projection
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact inclusion_projection S x
  · apply TopologicalSpace.Opens.ext
    change (PrimeSpectrum.comap (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A))) ⁻¹'
        Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away x))) =
      Set.range (PrimeSpectrum.comap (algebraMap (S ⊗[R] A)
        (Localization.Away ((1 : S) ⊗ₜ[R] x))))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away x) x,
      PrimeSpectrum.localization_away_comap_range _ ((1 : S) ⊗ₜ[R] x)]
    rfl

/-- The entire reverse boundary map is cartesian over its original integral map. -/
theorem transition_inv_isPullback :
    IsPullback ((transitionIso S x y e).inv ≫ inclusion S y) (projection S x)
      TensorOpenChart.projection
      (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away y)))) := by
  have H : IsPullback (transitionIso S x y e).inv (projection S x)
      (projection S y) (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := by
    change IsPullback _ _ _
      (Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op).hom
    exact IsPullback.of_horiz_isIso
      ⟨TensorOpenChart.transition_inv_projection S x y e⟩
  exact H.paste_horiz (inclusion_isPullback S y)

end FLT.Mazur.PrincipalOpenTensor
