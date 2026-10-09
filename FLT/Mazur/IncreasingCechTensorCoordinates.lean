/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechBaseComplex
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensor coordinates for the actual bounded Cech terms

Finite products distribute over arbitrary coefficient tensors. The coordinate
formula uses the original sheaf restrictions, without a flatness assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry TensorProduct
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex FCurve Chow CechSheafHZero

variable {X : Scheme} {ι : Type} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type} [CommRing R]
  (ρ : R →+* Γ(X, ⊤))

/-- Coordinates of an actual term, retaining its original base-ring action. -/
def baseTermCoordinates (n : ℕ) :
    BaseTerm M U ρ n ≃ₗ[R]
      (∀ a : Tuple (ι := ι) n, baseSections M ρ (V U n a.val)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual differential in section coordinates is the signed restriction sum. -/
lemma baseD_coordinates (n : ℕ) (x : BaseTerm M U ρ n)
    (a : Tuple (ι := ι) (n + 1)) :
    baseTermCoordinates M U ρ (n + 1) (baseD M U ρ n x) a =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        baseRestriction M ρ (face_le U n a.val k)
          (baseTermCoordinates M U ρ n x (face a k)) := by
  change ((complex U (moduleAbelianSheaf M)).d n (n + 1) x) a = _
  dsimp only [complex]
  rw [CochainComplex.of_d]
  exact differential_apply U (moduleAbelianSheaf M) n x a

variable [Finite ι] (B : Type) [AddCommGroup B] [Module R B]

/-- Arbitrary coefficient tensors of the actual term distribute over increasing charts. -/
def tensorCoordinates (n : ℕ) :
    B ⊗[R] BaseTerm M U ρ n ≃ₗ[R]
      (∀ a : Tuple (ι := ι) n, B ⊗[R] baseSections M ρ (V U n a.val)) := by
  let _ := Fintype.ofFinite (Tuple (ι := ι) n)
  exact (TensorProduct.congr (LinearEquiv.refl R B) (baseTermCoordinates M U ρ n)).trans
    (piRight R R B _)

/-- Pure tensors use their original increasing chart coordinate. -/
lemma tensorCoordinates_tmul (n : ℕ) (b : B) (x : BaseTerm M U ρ n)
    (a : Tuple (ι := ι) n) :
    tensorCoordinates M U ρ B n (b ⊗ₜ[R] x) a =
      b ⊗ₜ[R] baseTermCoordinates M U ρ n x a := rfl

/-- Tensor differentials retain the original signed chart restrictions. -/
lemma tensorD_coordinates (n : ℕ) (x : B ⊗[R] BaseTerm M U ρ n)
    (a : Tuple (ι := ι) (n + 1)) :
    tensorCoordinates M U ρ B (n + 1) ((baseD M U ρ n).lTensor B x) a =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (baseRestriction M ρ (face_le U n a.val k)).lTensor B
          (tensorCoordinates M U ρ B n x (face a k)) := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
    simp only [LinearMap.lTensor_tmul, tensorCoordinates_tmul, baseD_coordinates,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]

end FLT.Mazur.IncreasingCechScalars
