/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorCoefficientMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Cartesian coefficient changes of affine tensor charts

The map that changes coefficients and fixes the original affine functions is
an actual base change. Surjectivity on coefficient spectra therefore lifts to
the entire tensor chart, without reducing its source algebra.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.TensorCoefficientMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
  [Algebra R S] [Algebra R T] [Algebra R A]

/-- The two original tensor projections form the coefficient pullback square. -/
theorem tensorProjection_isPullback :
    IsPullback (TensorOpenChart.projection (R := R) (S := S) (A := A))
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply IsPullback.flip
  exact IsPullback.of_iso_pullback ⟨by
    rw [TensorOpenChart.projection, ← pullbackSpecIso_inv_fst' R S A,
      ← pullbackSpecIso_inv_snd R S A]
    simp only [Category.assoc, pullback.condition]⟩
    (pullbackSpecIso R S A).symm (pullbackSpecIso_inv_fst' R S A)
      (pullbackSpecIso_inv_snd R S A)

variable (f : S →ₐ[R] T)

/-- The specified coefficient map forms a Cartesian square with both structure maps. -/
theorem spectrum_isPullback :
    IsPullback (spectrum (A := A) f)
      (Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  apply IsPullback.of_right (h₁₂ := TensorOpenChart.projection)
    (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap R S))) _
    (spectrum_structure f) tensorProjection_isPullback
  rw [spectrum_projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hf : f.toRingHom.comp (algebraMap R S) = algebraMap R T := f.comp_algebraMap
  rw [hf]
  exact tensorProjection_isPullback

/-- Surjectivity of the base spectrum persists on every full affine tensor chart. -/
theorem spectrum_surjective
    [Surjective (Spec.map (CommRingCat.ofHom f.toRingHom))] :
    Surjective (spectrum (A := A) f) :=
  MorphismProperty.of_isPullback (spectrum_isPullback (A := A) f).flip inferInstance

/-- Coefficient change preserves membership of every original affine function in a prime. -/
theorem spectrum_tmul_mem (a : A) (q : Spec (.of (T ⊗[R] A))) :
    (1 : S) ⊗ₜ[R] a ∈ (spectrum f q).asIdeal ↔ (1 : T) ⊗ₜ[R] a ∈ q.asIdeal := by
  change algebra f ((1 : S) ⊗ₜ[R] a) ∈ q.asIdeal ↔ _
  rw [algebra_tmul, map_one]

end FLT.Mazur.TensorCoefficientMap
