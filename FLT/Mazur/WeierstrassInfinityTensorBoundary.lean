/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTensorYBoundary
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# The whole original Y-boundary as the tensor infinity principal open

Tensor the original Y/Z transition, retaining the entire overlap algebra.
Its comparison with the infinity localization preserves original functions
before any residue normalization or component decomposition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (S : Type u) [CommRing S] [Algebra R S]
local notation "z" => coord W 1 2
local notation "T" => S ⊗[R] Coordinate W 1
local notation "L" => Localization.Away ((1 : S) ⊗ₜ[R] z)

/-- The actual original affine Y-boundary is the full infinity Z-localization. -/
def infinityTensorBoundaryEquiv : S ⊗[R] Overlap W 2 1 ≃ₐ[S] L :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (overlapEquiv W 1 2)).trans
    (PrincipalOpenTensor.equiv S z)

/-- The boundary comparison retains every original localized function. -/
theorem infinityTensorBoundaryEquiv_tmul (s : S) (f : Overlap W 2 1) :
    infinityTensorBoundaryEquiv W S (s ⊗ₜ[R] f) =
      s • PrincipalOpenTensor.coefficient S z (overlapEquiv W 1 2 f) := by
  change PrincipalOpenTensor.equiv S z
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (overlapEquiv W 1 2) (s ⊗ₜ[R] f)) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  exact PrincipalOpenTensor.equiv_tmul S z s _

/-- The complete tensor overlap and the infinity principal open are isomorphic. -/
def infinityTensorBoundaryIso : Spec (.of L) ≅ Spec (.of (S ⊗[R] Overlap W 2 1)) :=
  Scheme.Spec.mapIso (infinityTensorBoundaryEquiv W S).toRingEquiv.toCommRingCatIso.op

/-- Projection keeps the original Y/Z coordinate transition on the whole boundary. -/
@[reassoc] theorem infinityTensorBoundaryIso_projection :
    (infinityTensorBoundaryIso W S).hom ≫ TensorOpenChart.projection =
      PrincipalOpenTensor.projection S z ≫ chartTransition W 1 2 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The complete boundary comparison also retains the extended coefficient structure. -/
@[reassoc] theorem infinityTensorBoundaryIso_structure :
    (infinityTensorBoundaryIso W S).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] Overlap W 2 1))) =
        Spec.map (CommRingCat.ofHom (algebraMap S L)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (infinityTensorBoundaryEquiv W S).commutes)

/-- The original full boundary map becomes the canonical infinity principal inclusion. -/
@[reassoc] theorem infinityTensorBoundaryIso_inclusion :
    (infinityTensorBoundaryIso W S).hom ≫
      WeierstrassDividedDepth.tensorBoundaryToInfinity (W := W) S =
        PrincipalOpenTensor.inclusion S z := by
  apply (cancel_mono (pullbackSpecIso R S (Coordinate W 1)).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [pullbackSpecIso_inv_fst',
      WeierstrassDividedDepth.tensorBoundaryToInfinity_structure,
      infinityTensorBoundaryIso_structure, PrincipalOpenTensor.inclusion_structure]
  · simp only [Category.assoc]
    rw [pullbackSpecIso_inv_snd]
    change (infinityTensorBoundaryIso W S).hom ≫
      WeierstrassDividedDepth.tensorBoundaryToInfinity (W := W) S ≫
        TensorOpenChart.projection = PrincipalOpenTensor.inclusion S z ≫
          TensorOpenChart.projection
    rw [WeierstrassDividedDepth.tensorBoundaryToInfinity_projection,
      infinityTensorBoundaryIso_projection_assoc, PrincipalOpenTensor.inclusion_projection]
    rw [affineBoundaryToY, ← Category.assoc (chartTransition W 1 2)]
    have ht : chartTransition W 1 2 ≫ chartTransition W 2 1 = 𝟙 _ := by
      change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      exact congrArg (fun f : Overlap W 1 2 →ₐ[R] Overlap W 1 2 =>
        CommRingCat.ofHom f.toRingHom) (transition_comp W 1 2)
    rw [ht, Category.id_comp]
    rfl

end FLT.Mazur.WeierstrassIntegralChart
