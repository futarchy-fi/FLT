/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Component ideals under actual atlas embeddings

An open atlas embedding does not change the inverse image of an affine
closed locus: it is computed by the full ideal map on the source algebra.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.SpecChartIdeal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
  (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] (f : A →+* B) (I : Ideal A)

/-- Ideal pullback retains its full closed locus after inclusion in an arbitrary atlas. -/
theorem preimage_image_zeroLocus :
    (Spec.map (CommRingCat.ofHom f) ≫ i) ⁻¹' (i '' PrimeSpectrum.zeroLocus (I : Set A)) =
      PrimeSpectrum.zeroLocus (Ideal.map f I : Set B) := by
  change (i ∘ PrimeSpectrum.comap f) ⁻¹' (i '' PrimeSpectrum.zeroLocus (I : Set A)) = _
  rw [Set.preimage_comp, Set.preimage_image_eq _ i.isOpenEmbedding.injective,
    PrimeSpectrum.preimage_comap_zeroLocus, ← PrimeSpectrum.zeroLocus_span]
  rfl

end FLT.Mazur.SpecChartIdeal
