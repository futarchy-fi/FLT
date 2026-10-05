/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTensorCocycle

/-!
# Canonical tensor cocycles and transport along module isomorphisms

Scalar extensions carry their canonical overlap cocycle. Module isomorphisms
transport the entire cocycle, including the second scalar action.
-/

@[expose] public noncomputable section

open TensorProduct

universe u

namespace FLT.Mazur.AffineTensorCocycle

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The overlap isomorphism of a scalar extension keeps its first scalar factor. -/
def canonicalOverlap (M : Type u) [AddCommGroup M] [Module R M] :
    (S ⊗[R] M) ⊗[R] S ≃ₗ[S] S ⊗[R] (S ⊗[R] M) :=
  AlgebraTensorModule.assoc R R S S M S ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl S S) (TensorProduct.comm R M S)

/-- The canonical overlap sends `(a ⊗ m) ⊗ b` to `a ⊗ (b ⊗ m)`. -/
@[simp]
theorem canonicalOverlap_tmul (M : Type u) [AddCommGroup M] [Module R M]
    (a b : S) (m : M) : canonicalOverlap M ((a ⊗ₜ[R] m) ⊗ₜ[R] b) =
      a ⊗ₜ[R] (b ⊗ₜ[R] m) := rfl

/-- The actual diagonal and cocycle identities for scalar extension. -/
def canonicalDatum (M : Type u) [AddCommGroup M] [Module R M] :
    Datum R S (S ⊗[R] M) where
  overlap := canonicalOverlap M
  other_smul n s t := by
    induction n using TensorProduct.inductionOn with
    | tmul a m => simp [smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  diagonal n := by
    induction n using TensorProduct.inductionOn with
    | tmul a m => simp [smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  cocycle n s t := by
    induction n using TensorProduct.inductionOn with
    | tmul a m => rfl
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]

variable {N P : Type u} [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

/-- Transport the double-overlap isomorphism along a coefficient isomorphism. -/
def transportOverlap (D : Datum R S N) (e : N ≃ₗ[S] P) :
    P ⊗[R] S ≃ₗ[S] S ⊗[R] P :=
  AlgebraTensorModule.congr e.symm (LinearEquiv.refl R S) ≪≫ₗ D.overlap ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl S S) (e.restrictScalars R)

/-- The transported overlap has the expected formula on generators. -/
@[simp]
theorem transportOverlap_tmul (D : Datum R S N) (e : N ≃ₗ[S] P) (n : P) (s : S) :
    transportOverlap D e (n ⊗ₜ[R] s) =
      (e.toLinearMap.restrictScalars R).lTensor S (D.overlap (e.symm n ⊗ₜ[R] s)) := rfl

/-- Coefficient isomorphisms transport all the overlap descent equations. -/
def transportDatum (D : Datum R S N) (e : N ≃ₗ[S] P) : Datum R S P where
  overlap := transportOverlap D e
  other_smul n s t := by
    simp only [transportOverlap_tmul, D.other_smul]
    generalize D.overlap (e.symm n ⊗ₜ[R] t) = x
    induction x using TensorProduct.inductionOn with
    | tmul a m => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  diagonal n := by
    rw [transportOverlap_tmul]
    have h (x : S ⊗[R] N) :
        TensorProduct.lift (Algebra.lsmul R R P (A := S)).toLinearMap
          ((e.toLinearMap.restrictScalars R).lTensor S x) =
        e (TensorProduct.lift (Algebra.lsmul R R N (A := S)).toLinearMap x) := by
      induction x using TensorProduct.inductionOn with
      | tmul a m => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [h, D.diagonal, e.apply_symm_apply]
  cocycle n s t := by
    have h (x : S ⊗[R] N) :
        ((transportOverlap D e).toLinearMap.restrictScalars R).lTensor S
          ((TensorProduct.assoc R S P S)
            (((e.toLinearMap.restrictScalars R).lTensor S x) ⊗ₜ[R] t)) =
        ((e.toLinearMap.restrictScalars R).lTensor S).lTensor S
          ((D.overlap.toLinearMap.restrictScalars R).lTensor S
            ((TensorProduct.assoc R S N S) (x ⊗ₜ[R] t))) := by
      induction x using TensorProduct.inductionOn with
      | tmul a m => simp
      | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
    change ((transportOverlap D e).toLinearMap.restrictScalars R).lTensor S
      ((TensorProduct.assoc R S P S) ((transportOverlap D e (n ⊗ₜ[R] s)) ⊗ₜ[R] t)) = _
    rw [transportOverlap_tmul, h]
    change ((e.toLinearMap.restrictScalars R).lTensor S).lTensor S
      (transportTwice D.overlap ((e.symm n ⊗ₜ[R] s) ⊗ₜ[R] t)) = _
    rw [D.cocycle, transportOverlap_tmul]
    generalize D.overlap (e.symm n ⊗ₜ[R] t) = x
    induction x using TensorProduct.inductionOn with
    | tmul a m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Transport of the cocycle transports the coaction by the same isomorphism. -/
theorem transportDatum_coaction (D : Datum R S N) (e : N ≃ₗ[S] P) (n : P) :
    (transportDatum D e).coaction n =
      (e.toLinearMap.restrictScalars R).lTensor S (D.coaction (e.symm n)) := rfl

end FLT.Mazur.AffineTensorCocycle
