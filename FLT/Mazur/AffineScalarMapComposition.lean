/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineScalarMap

/-!
# Composition and faithfulness for spectra of algebra maps

These helpers expose the contravariant composition rule without unfolding
concrete algebra maps during geometric naturality arguments.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineScalarMap

universe u

variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]

/-- Spectrum reverses composition of algebra maps. -/
theorem spec_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U) :
    Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) :=
  Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)

/-- Equality of affine scheme maps detects equality of the full algebra maps. -/
theorem spec_injective {f g : S →ₐ[R] T}
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom g.toRingHom)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end FLT.Mazur.AffineScalarMap
