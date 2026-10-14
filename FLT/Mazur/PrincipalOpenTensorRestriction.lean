/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# Original function restriction to a tensor principal open

The tensor of the integral restriction is an open immersion. Its formula on
pure tensors retains every original function, including the divided coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {A : Type u} [CommRing A] [Algebra R A] (x : A)

/-- Restriction of original tensor functions to the tensor of the integral localization. -/
def restriction : S ⊗[R] A →ₐ[S] S ⊗[R] Localization.Away x :=
  (equiv (R := R) S x).symm.toAlgHom.comp (IsScalarTower.toAlgHom S (S ⊗[R] A) _)

/-- Every original function restricts before or after coefficient extension identically. -/
@[simp] theorem restriction_tmul (s : S) (a : A) :
    restriction (R := R) S x (s ⊗ₜ[R] a) = s ⊗ₜ[R] algebraMap A (Localization.Away x) a := by
  apply (equiv (R := R) S x).injective
  exact ((equiv (R := R) S x).apply_symm_apply _).trans (equiv_tmul_base (R := R) S x s a).symm

/-- Normalizing restriction is exactly the principal localization map. -/
@[simp] theorem equiv_restriction (z : S ⊗[R] A) :
    equiv (R := R) S x (restriction (R := R) S x z) = algebraMap (S ⊗[R] A) _ z :=
  (equiv (R := R) S x).apply_symm_apply _

/-- The actual horizontal tensor inclusion in its full original tensor chart. -/
def tensorInclusion : Spec (.of (S ⊗[R] Localization.Away x)) ⟶
    Spec (.of (S ⊗[R] A)) := Spec.map (CommRingCat.ofHom (restriction (R := R) S x).toRingHom)

/-- The tensor inclusion is the principal inclusion after the canonical tensor comparison. -/
theorem tensorInclusion_eq : tensorInclusion (R := R) S x =
    (Scheme.Spec.mapIso (equiv (R := R) S x).toRingEquiv.toCommRingCatIso.op).inv ≫
      inclusion (R := R) S x := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

instance tensorInclusion_isOpenImmersion : IsOpenImmersion (tensorInclusion (R := R) S x) := by
  rw [tensorInclusion_eq]
  infer_instance

end FLT.Mazur.PrincipalOpenTensor
