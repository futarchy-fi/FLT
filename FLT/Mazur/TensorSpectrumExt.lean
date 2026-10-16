/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorCoefficientMap

/-!
# Detecting morphisms into the full tensor spectrum

The coefficient and original affine projections jointly determine a map.
This permits coefficient squares to be checked without expanding tensor algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- Both tensor projections determine an arbitrary scheme morphism into the tensor spectrum. -/
theorem spectrum_hom_ext {X : Scheme.{u}} (g h : X ⟶ Spec (.of (S ⊗[R] A)))
    (hc : g ≫ Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
      h ≫ Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
    (ha : g ≫ projection = h ≫ projection) : g = h := by
  apply (cancel_mono (pullbackSpecIso R S A).inv).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullbackSpecIso_inv_fst'] using hc
  · simpa only [Category.assoc, pullbackSpecIso_inv_snd, projection] using ha

end FLT.Mazur.TensorOpenChart
