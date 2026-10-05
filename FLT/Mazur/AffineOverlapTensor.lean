/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Coefficients of the two affine overlap projections

Extension along the two inclusions into `S ⊗[R] S` identifies with the two
ordered tensor products of an `S`-module. Pure tensor formulas record both
scalar actions, including the action not encoded by linearity over `S`.
-/

@[expose] public noncomputable section
open CategoryTheory TensorProduct
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffineOverlapTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- First coefficient inclusion into the overlap ring. -/
abbrev left : S →+* S ⊗[R] S := Algebra.TensorProduct.includeLeftRingHom

/-- Second coefficient inclusion into the overlap ring. -/
abbrev right : S →+* S ⊗[R] S := ↑(Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)

variable (N : Type u) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Cancel the first projection's scalar extension. -/
def first : ((S ⊗[R] S) ⊗[S] N) ≃ₗ[S] N ⊗[R] S :=
  TensorProduct.comm S (S ⊗[R] S) N ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange R S S N S

@[simp]
theorem first_tmul (s t : S) (n : N) :
    first R S N ((s ⊗ₜ[R] t) ⊗ₜ[S] n) = (s • n) ⊗ₜ[R] t := rfl

@[simp]
theorem first_symm_tmul (n : N) (s : S) :
    (first R S N).symm (n ⊗ₜ[R] s) = (1 ⊗ₜ[R] s) ⊗ₜ[S] n := rfl

/-- Restricting the overlap ring along the first inclusion gives its usual scalar action. -/
def leftIdentity :
    (ModuleCat.restrictScalars (left R S)).obj (ModuleCat.of (S ⊗[R] S) (S ⊗[R] S)) ≃ₗ[S]
      S ⊗[R] S where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' s x := (Algebra.smul_def (A := S ⊗[R] S) s x).symm

/-- First projection comparison on the bundled scalar extension. -/
def firstExtension :
    ((ModuleCat.extendScalars (left R S)).obj (ModuleCat.of S N)) ≃+ N ⊗[R] S :=
  (TensorProduct.congr (leftIdentity R S) (LinearEquiv.refl S N) ≪≫ₗ first R S N).toAddEquiv

@[simp]
theorem firstExtension_tmul (s t : S) (n : N) :
    firstExtension R S N ((s ⊗ₜ[R] t) ⊗ₜ[S,left R S] n) = (s • n) ⊗ₜ[R] t := rfl

@[simp]
theorem firstExtension_symm_tmul (n : N) (s : S) :
    (firstExtension R S N).symm (n ⊗ₜ[R] s) = (1 ⊗ₜ[R] s) ⊗ₜ[S,left R S] n := rfl

/-- Swap identifies the second scalar structure with the first one. -/
def rightSwap :
    (ModuleCat.restrictScalars (right R S)).obj (ModuleCat.of (S ⊗[R] S) (S ⊗[R] S)) ≃ₗ[S]
      S ⊗[R] S where
  toFun := Algebra.TensorProduct.comm R S S
  invFun := Algebra.TensorProduct.comm R S S
  map_add' := map_add _
  map_smul' s x := by
    exact (map_mul (Algebra.TensorProduct.comm R S S) ((1 : S) ⊗ₜ[R] s) x).trans
      (Algebra.smul_def (A := S ⊗[R] S) s (Algebra.TensorProduct.comm R S S x)).symm
  left_inv := (Algebra.TensorProduct.comm R S S).left_inv
  right_inv := (Algebra.TensorProduct.comm R S S).right_inv

/-- Cancel the second projection's scalar extension, keeping tensor order explicit. -/
def second : ((ModuleCat.extendScalars (right R S)).obj (ModuleCat.of S N)) ≃+ S ⊗[R] N :=
  ((TensorProduct.congr (rightSwap R S) (LinearEquiv.refl S N) ≪≫ₗ first R S N).toAddEquiv).trans
    (TensorProduct.comm R N S).toAddEquiv

@[simp]
theorem second_tmul (s t : S) (n : N) :
    second R S N ((s ⊗ₜ[R] t) ⊗ₜ[S,right R S] n) = s ⊗ₜ[R] (t • n) := rfl

@[simp]
theorem second_symm_tmul (s : S) (n : N) :
    (second R S N).symm (s ⊗ₜ[R] n) = (s ⊗ₜ[R] 1) ⊗ₜ[S,right R S] n := rfl

/-- The first identification preserves the complete overlap-ring action on generators. -/
theorem firstExtension_symm_smul_tmul (a b t : S) (n : N) :
    (a ⊗ₜ[R] b) • (firstExtension R S N).symm (n ⊗ₜ[R] t) =
      (firstExtension R S N).symm ((a • n) ⊗ₜ[R] (b * t)) := by
  change ((a ⊗ₜ[R] b) * ((1 : S) ⊗ₜ[R] t)) ⊗ₜ[S,left R S] n =
    ((1 : S) ⊗ₜ[R] (b * t)) ⊗ₜ[S,left R S] (a • n)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  change (a ⊗ₜ[R] (b * t)) ⊗ₜ[S,left R S] n = (1 ⊗ₜ[R] (b * t)) ⊗ₜ[S,left R S] (a • n)
  rw [← smul_tmul (R := S) (M := (ModuleCat.restrictScalars (left R S)).obj
    (ModuleCat.of (S ⊗[R] S) (S ⊗[R] S)))]
  change _ = (((a ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] (b * t))) ⊗ₜ[S,left R S] n)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The second identification preserves the complete overlap-ring action on generators. -/
theorem second_symm_smul_tmul (a b t : S) (n : N) :
    (a ⊗ₜ[R] b) • (second R S N).symm (t ⊗ₜ[R] n) =
      (second R S N).symm ((a * t) ⊗ₜ[R] (b • n)) := by
  change ((a ⊗ₜ[R] b) * (t ⊗ₜ[R] (1 : S))) ⊗ₜ[S,right R S] n =
    ((a * t) ⊗ₜ[R] (1 : S)) ⊗ₜ[S,right R S] (b • n)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  change ((a * t) ⊗ₜ[R] b) ⊗ₜ[S,right R S] n =
    ((a * t) ⊗ₜ[R] 1) ⊗ₜ[S,right R S] (b • n)
  rw [← smul_tmul (R := S) (M := (ModuleCat.restrictScalars (right R S)).obj
    (ModuleCat.of (S ⊗[R] S) (S ⊗[R] S)))]
  change ((a * t) ⊗ₜ[R] b) ⊗ₜ[S,right R S] n =
    ((1 ⊗ₜ[R] b) * ((a * t) ⊗ₜ[R] 1)) ⊗ₜ[S,right R S] n
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end FLT.Mazur.AffineOverlapTensor
