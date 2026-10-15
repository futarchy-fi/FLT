/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineScalarFiberComparison
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Actual affine coordinates and integral scalar fibers

The original structure morphism defines the section algebra. Its tensor
spectrum is the actual field fiber, so geometric integrality proves the
integral tensor premise required for transcendental coefficient avoidance.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.OriginalAffineFiberCoordinates
open AffineScalarFiberComparison
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] {X : Scheme} [IsAffine X] (f : X ⟶ Spec (.of k))

/-- The actual affine coordinate morphism is recovered from the original base map. -/
theorem coordinate_map :
    let _ := (scalarMap f).toAlgebra
    Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤))) = X.isoSpec.inv ≫ f := by
  let _ := (scalarMap f).toAlgebra
  dsimp only
  conv_rhs => rw [factorization f]
  simp only [Iso.inv_hom_id_assoc]
  rfl

/-- Local finite type supplies finite type of the original section algebra. -/
theorem sections_finiteType [LocallyOfFiniteType f] :
    let _ := (scalarMap f).toAlgebra
    Algebra.FiniteType k Γ(X, ⊤) := by
  let _ := (scalarMap f).toAlgebra
  have hf : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap k Γ(X, ⊤)))) := by
    rw [coordinate_map]
    infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hf

/-- Cartesian squares survive conversion to the original affine section coordinates. -/
theorem coordinate_square {K : Type} [Field K] [Algebra k K] {Y : Scheme}
    (a : Y ⟶ Spec (.of K)) (b : Y ⟶ X)
    (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) :
    let _ := (scalarMap f).toAlgebra
    IsPullback a (b ≫ X.isoSpec.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))) := by
  let _ := (scalarMap f).toAlgebra
  apply H.of_iso (Iso.refl _) (Iso.refl _) X.isoSpec (Iso.refl _)
  · simp
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, coordinate_map, Iso.hom_inv_id_assoc]

/-- The tensor spectrum is an actual field fiber of the original affine scheme. -/
theorem tensor_square (L : Type) [Field L] [Algebra k L] :
    let _ := (scalarMap f).toAlgebra
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[k] Γ(X, ⊤)))))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[k] L ⊗[k] Γ(X, ⊤)).toRingHom) ≫
        X.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f := by
  let _ := (scalarMap f).toAlgebra
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct k L Γ(X, ⊤))
  apply H.of_iso (Iso.refl _) (Iso.refl _) X.isoSpec.symm (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    exact coordinate_map f

/-- Geometric integrality proves the domain premise for every extended coordinate algebra. -/
theorem tensor_isDomain [GeometricallyIntegral f] (L : Type) [Field L] [Algebra k L] :
    let _ := (scalarMap f).toAlgebra
    IsDomain (L ⊗[k] Γ(X, ⊤)) := by
  let _ := (scalarMap f).toAlgebra
  have : IsIntegral (Spec (.of (L ⊗[k] Γ(X, ⊤)))) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (tensor_square f L).flip
  exact (affine_isIntegral_iff _).mp this

end FLT.Mazur.OriginalAffineFiberCoordinates
