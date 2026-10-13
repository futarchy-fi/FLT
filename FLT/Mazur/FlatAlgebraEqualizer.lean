/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatTensorEqualizer
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Multiplicative descent of coefficient equalizers under flat base change

The tensor product of the actual original invariant algebra is isomorphic,
as an algebra over the new coefficient ring, to the full equalizer of the
two base-changed coefficient maps. The comparison is the tensor inclusion.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatAlgebraEqualizer
variable {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]
  [Algebra R A] [Algebra R C] (p q : A →ₐ[R] C)
  (B : Type*) [CommRing B] [Algebra R B]

/-- Extend an original coefficient homomorphism by the identity on the new base. -/
def tensorMap (g : A →ₐ[R] C) : B ⊗[R] A →ₐ[B] B ⊗[R] C :=
  Algebra.TensorProduct.map (AlgHom.id B B) g

/-- The algebra map is the underlying flat tensor map on every coefficient. -/
theorem tensorMap_eq_lTensor (g : A →ₐ[R] C) (x : B ⊗[R] A) :
    tensorMap B g x = g.toLinearMap.lTensor B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Original invariant coefficients, with their actual kernel module structure. -/
def kernelEquiv : AlgHom.equalizer p q ≃ₗ[R]
    FlatTensorEqualizer.equalizer p.toLinearMap q.toLinearMap where
  toFun a := ⟨a.val, (FlatTensorEqualizer.mem_equalizer _ _ _).mpr a.property⟩
  invFun a := ⟨a.val, (FlatTensorEqualizer.mem_equalizer _ _ _).mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original invariant inclusion, extended over the new coefficient algebra. -/
def tensorInclusion : B ⊗[R] AlgHom.equalizer p q →ₐ[B] B ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id B B) (AlgHom.equalizer p q).val

/-- The inclusion satisfies both full tensor equations without a flatness assumption. -/
theorem tensorInclusion_equal (x : B ⊗[R] AlgHom.equalizer p q) :
    tensorMap B p (tensorInclusion p q B x) =
      tensorMap B q (tensorInclusion p q B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b a => exact congrArg (fun c ↦ b ⊗ₜ[R] c) a.property
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual algebra comparison to the full tensor equalizer. -/
def comparisonMap : B ⊗[R] AlgHom.equalizer p q →ₐ[B]
    AlgHom.equalizer (tensorMap B p) (tensorMap B q) :=
  (tensorInclusion p q B).codRestrict _ (tensorInclusion_equal p q B)

/-- The tensor inclusion agrees with the original kernel inclusion on every tensor. -/
theorem inclusion_kernel (x : B ⊗[R] AlgHom.equalizer p q) :
    tensorInclusion p q B x =
      (FlatTensorEqualizer.equalizer p.toLinearMap q.toLinearMap).subtype.lTensor B
        ((kernelEquiv p q).lTensor B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Module.Flat R B]

/-- Flatness makes the actual multiplicative comparison injective. -/
theorem comparisonMap_injective : Function.Injective (comparisonMap p q B) := by
  intro x y h
  apply (kernelEquiv p q).lTensor B |>.injective
  apply FlatTensorEqualizer.inclusion_injective p.toLinearMap q.toLinearMap B
  rw [← inclusion_kernel, ← inclusion_kernel]
  exact congrArg Subtype.val h

/-- Every coefficient satisfying both full tensor equations descends from original invariants. -/
theorem comparisonMap_surjective : Function.Surjective (comparisonMap p q B) := by
  intro x
  have hx : p.toLinearMap.lTensor B x.val = q.toLinearMap.lTensor B x.val := by
    rw [← tensorMap_eq_lTensor, ← tensorMap_eq_lTensor]
    exact x.property
  obtain ⟨y, hy, _⟩ := FlatTensorEqualizer.existsUnique_lift
    p.toLinearMap q.toLinearMap B x.val hx
  refine ⟨((kernelEquiv p q).lTensor B).symm y, Subtype.ext ?_⟩
  change tensorInclusion p q B _ = _
  rw [inclusion_kernel, LinearEquiv.apply_symm_apply, hy]

/-- Flat scalar extension commutes with the full original algebra equalizer. -/
def comparison : B ⊗[R] AlgHom.equalizer p q ≃ₐ[B]
    AlgHom.equalizer (tensorMap B p) (tensorMap B q) :=
  AlgEquiv.ofBijective (comparisonMap p q B)
    ⟨comparisonMap_injective p q B, comparisonMap_surjective p q B⟩

/-- The algebra isomorphism retains the exact original pure tensor coefficients. -/
theorem comparison_tmul (b : B) (a : AlgHom.equalizer p q) :
    (comparison p q B (b ⊗ₜ[R] a)).val = b ⊗ₜ[R] a.val := rfl

end FLT.Mazur.FlatAlgebraEqualizer
