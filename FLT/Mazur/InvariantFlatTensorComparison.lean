/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantFlatTensorAction
public import FLT.Mazur.FlatTensorFixedSubmodule

/-!
# The actual invariant-ring comparison under flat base change

For a flat algebra over the invariant ring, the fixed ring of its tensor
product with the original ring is canonically the new base algebra. The
comparison is the actual scalar map, with injectivity and surjectivity proved
from flatness and finite simultaneous fixed-point exactness.
-/

@[expose] public noncomputable section

open TensorProduct

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A]

/-- The original action as endomorphisms linear over the actual invariant ring. -/
def invariantLinearAction (g : G) : A →ₗ[invariantRing G A] A :=
  (MulSemiringAction.toAlgHom (invariantRing G A) A g).toLinearMap

/-- The fixed ring, as a module over itself, is the simultaneous fixed submodule. -/
def fixedLinearEquiv : invariantRing G A ≃ₗ[invariantRing G A]
    FlatTensorFixed.fixed (invariantLinearAction G A) where
  toFun a := ⟨a.val, (FlatTensorFixed.mem_fixed _ _).mpr a.property⟩
  invFun a := ⟨a.val, (FlatTensorFixed.mem_fixed _ _).mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (B : Type*) [CommRing B] [Algebra (invariantRing G A) B]

/-- The tensor inclusion of fixed elements is the actual new-base scalar map. -/
lemma tensor_fixed_scalar (t : B ⊗[invariantRing G A] invariantRing G A) :
    (FlatTensorFixed.fixed (invariantLinearAction G A)).subtype.lTensor B
      ((fixedLinearEquiv G A).lTensor B t) =
        algebraMap B (B ⊗[invariantRing G A] A) (TensorProduct.rid _ B t) := by
  induction t using TensorProduct.inductionOn with
  | tmul b a =>
      simp only [LinearEquiv.lTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, Algebra.TensorProduct.algebraMap_apply]
      change b ⊗ₜ[invariantRing G A] a.val = (a • b) ⊗ₜ[invariantRing G A] (1 : A)
      rw [TensorProduct.smul_tmul]
      simp only [Algebra.smul_def, mul_one]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Module.Flat (invariantRing G A) B]

/-- Flatness makes the canonical comparison into the actual fixed ring injective. -/
lemma tensorInvariantMap_injective :
    let _ := tensorAction G A B
    Function.Injective (tensorInvariantMap G A B) := by
  let _ := tensorAction G A B
  change Function.Injective (tensorInvariantMap G A B)
  intro b c h
  apply Algebra.TensorProduct.includeLeft_injective
    (R := invariantRing G A) (S := B) (A := B) (inclusion_injective G A)
  exact congrArg Subtype.val h

variable [Finite G]

/-- Finite simultaneous fixed-point exactness proves surjectivity of the fixed-ring comparison. -/
lemma tensorInvariantMap_surjective :
    let _ := tensorAction G A B
    Function.Surjective (tensorInvariantMap G A B) := by
  let _ := tensorAction G A B
  change Function.Surjective (tensorInvariantMap G A B)
  intro x
  have hx (g : G) : (invariantLinearAction G A g).lTensor B x.val = x.val := by
    rw [invariantLinearAction, ← tensorActionHom_eq_lTensor]
    exact x.property g
  obtain ⟨y, hy, _⟩ :=
    FlatTensorFixed.existsUnique_fixed_lift (invariantLinearAction G A) B x.val hx
  let t := (fixedLinearEquiv G A).symm.lTensor B y
  refine ⟨TensorProduct.rid _ B t, ?_⟩
  apply Subtype.ext
  rw [tensorInvariantMap_val, ← tensor_fixed_scalar]
  change (FlatTensorFixed.fixed (invariantLinearAction G A)).subtype.lTensor B
    ((fixedLinearEquiv G A).lTensor B
      (((fixedLinearEquiv G A).lTensor B).symm y)) = x.val
  rw [LinearEquiv.apply_symm_apply]
  exact hy

/-- Flat base change identifies the actual fixed ring with the new base ring. -/
def tensorInvariantEquiv :
    let _ := tensorAction G A B
    B ≃+* invariantRing G (B ⊗[invariantRing G A] A) := by
  let _ := tensorAction G A B
  exact RingEquiv.ofBijective (tensorInvariantMap G A B)
    ⟨tensorInvariantMap_injective G A B, tensorInvariantMap_surjective G A B⟩

/-- The isomorphism is the scalar map into tensor-product coordinates. -/
lemma tensorInvariantEquiv_val (b : B) :
    let _ := tensorAction G A B
    (tensorInvariantEquiv G A B b : B ⊗[invariantRing G A] A) =
      algebraMap B (B ⊗[invariantRing G A] A) b := rfl

end FLT.Mazur.FiniteGroupQuotient
