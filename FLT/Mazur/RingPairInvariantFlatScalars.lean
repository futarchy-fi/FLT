/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatAlgebraEqualizer

/-!
# Flat extension over the actual invariant ring of a pair of maps

For any two coefficient maps, a flat algebra over their original equalizer
is exactly the equalizer after extending both maps to that algebra. This
includes localization at an original invariant coefficient and requires no
group action, averaging, or quotient effectivity hypothesis.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.RingPairInvariantFlatScalars
variable {A C : Type*} [CommRing A] [CommRing C] (p q : A →+* C)

/-- The original invariant coefficient ring. -/
abbrev invariants := RingHom.eqLocus p q

/-- The original source is an algebra over its actual invariant ring. -/
@[instance_reducible]
def sourceAlgebra : Algebra (invariants p q) A := (invariants p q).subtype.toAlgebra

/-- Both relation coefficients use the same scalar map, by original invariance. -/
@[instance_reducible]
def targetAlgebra : Algebra (invariants p q) C :=
  (p.comp (invariants p q).subtype).toAlgebra

attribute [local instance] sourceAlgebra targetAlgebra

/-- The first coefficient homomorphism over the full invariant scalars. -/
def first : A →ₐ[invariants p q] C := ⟨p, fun _ ↦ rfl⟩

/-- The second coefficient homomorphism over the same full invariant scalars. -/
def second : A →ₐ[invariants p q] C := ⟨q, fun a ↦ a.property.symm⟩

/-- The original invariant ring is exactly the linear equalizer over itself. -/
def kernelEquiv : invariants p q ≃ₗ[invariants p q]
    FlatTensorEqualizer.equalizer (first p q).toLinearMap (second p q).toLinearMap where
  toFun a := ⟨a.val, (FlatTensorEqualizer.mem_equalizer _ _ _).mpr a.property⟩
  invFun a := ⟨a.val, (FlatTensorEqualizer.mem_equalizer _ _ _).mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (B : Type*) [CommRing B] [Algebra (invariants p q) B]
local notation "α" => FlatAlgebraEqualizer.tensorMap B (first p q)
local notation "β" => FlatAlgebraEqualizer.tensorMap B (second p q)

/-- Scalars in the new base satisfy both complete extended coefficient equations. -/
def scalarMap : B →+* AlgHom.equalizer α β :=
  (algebraMap B (B ⊗[invariants p q] A)).codRestrict _ (fun b ↦ by
    change α (algebraMap B _ b) = β (algebraMap B _ b)
    rw [AlgHom.commutes, AlgHom.commutes])

/-- The tensor of the invariant inclusion agrees with the actual new-base scalar map. -/
theorem tensor_scalar (t : B ⊗[invariants p q] invariants p q) :
    (FlatTensorEqualizer.equalizer (first p q).toLinearMap
      (second p q).toLinearMap).subtype.lTensor B ((kernelEquiv p q).lTensor B t) =
        algebraMap B (B ⊗[invariants p q] A) (TensorProduct.rid _ B t) := by
  induction t using TensorProduct.inductionOn with
  | tmul b a =>
      simp only [LinearEquiv.lTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        Algebra.TensorProduct.algebraMap_apply]
      change b ⊗ₜ[invariants p q] a.val = (a • b) ⊗ₜ[invariants p q] (1 : A)
      rw [TensorProduct.smul_tmul]
      simp only [Algebra.smul_def, mul_one]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Module.Flat (invariants p q) B]

/-- Flatness makes the new scalar map into the full equalizer injective. -/
theorem scalarMap_injective : Function.Injective (scalarMap p q B) := by
  intro b c h
  apply Algebra.TensorProduct.includeLeft_injective
    (R := invariants p q) (S := B) (A := B) Subtype.val_injective
  exact congrArg Subtype.val h

/-- Every full-invariant tensor is an actual scalar from the flat new base. -/
theorem scalarMap_surjective : Function.Surjective (scalarMap p q B) := by
  intro x
  have hx : (first p q).toLinearMap.lTensor B x.val =
      (second p q).toLinearMap.lTensor B x.val := by
    rw [← FlatAlgebraEqualizer.tensorMap_eq_lTensor, ← FlatAlgebraEqualizer.tensorMap_eq_lTensor]
    exact x.property
  obtain ⟨y, hy, _⟩ := FlatTensorEqualizer.existsUnique_lift
    (first p q).toLinearMap (second p q).toLinearMap B x.val hx
  let t := ((kernelEquiv p q).lTensor B).symm y
  refine ⟨TensorProduct.rid _ B t, Subtype.ext ?_⟩
  change algebraMap B (B ⊗[invariants p q] A) _ = _
  rw [← tensor_scalar]
  dsimp only [t]
  rw [LinearEquiv.apply_symm_apply, hy]

/-- The flat new base is exactly the full equalizer of the two extended original maps. -/
def scalarEquiv : B ≃+* AlgHom.equalizer α β :=
  RingEquiv.ofBijective (scalarMap p q B)
    ⟨scalarMap_injective p q B, scalarMap_surjective p q B⟩

/-- The comparison retains the actual scalar inclusion, rather than an abstract ring isomorphism. -/
theorem scalarEquiv_val (b : B) :
    (scalarEquiv p q B b).val = algebraMap B (B ⊗[invariants p q] A) b := rfl

end FLT.Mazur.RingPairInvariantFlatScalars
