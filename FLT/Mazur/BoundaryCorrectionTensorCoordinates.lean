/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionFlatReconstruction
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Actual independent coefficient coordinates for the ambient correction system

For a finite chart index, tensoring the original system is exactly the system
on the separately extended chart, boundary, and mixed coefficient modules.
The scalar remains in the extension of the original scalar ring.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (S : Type*) [CommRing S] [Algebra R S]

/-- Separate the original scalar and all independently extended chart coefficients. -/
def tensorCorrectionCoordinates : (S ⊗[R] (R × ∀ i, A i)) ≃ₗ[R]
    S × ∀ i, S ⊗[R] A i := by
  classical
  exact (prodRight R R S R (∀ i, A i)).trans
    ((TensorProduct.rid R S).prodCongr (piRight R R S A))

/-- Separate every exact boundary equation and every independent mixed equation. -/
def tensorCorrectionTarget : (S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)) ≃ₗ[R]
    (∀ i, S ⊗[R] B i) × ∀ i j, S ⊗[R] C i j := by
  classical
  exact (prodRight R R S (∀ i, B i) (∀ i j, C i j)).trans
    ((piRight R R S B).prodCongr ((piRight R R S (fun i ↦ ∀ j, C i j)).trans
      (LinearEquiv.piCongrRight fun i ↦ piRight R R S (C i))))

/-- Pure chart tensors have their literal independent coefficients. -/
theorem tensorCorrectionCoordinates_tmul (s : S) (x : R × ∀ i, A i) :
    tensorCorrectionCoordinates (A := A) S (s ⊗ₜ[R] x) =
      (algebraMap R S x.1 * s, fun i ↦ s ⊗ₜ[R] x.2 i) := by
  classical
  simp only [tensorCorrectionCoordinates, LinearEquiv.trans_apply, prodRight_tmul,
    LinearEquiv.prodCongr_apply, rid_tmul, Algebra.smul_def, piRight_apply, piRightHom_tmul]

/-- Pure equation tensors retain all original boundary and mixed coefficients. -/
theorem tensorCorrectionTarget_tmul (s : S) (x : (∀ i, B i) × ∀ i j, C i j) :
    tensorCorrectionTarget (B := B) (C := C) S (s ⊗ₜ[R] x) =
      (fun i ↦ s ⊗ₜ[R] x.1 i, fun i j ↦ s ⊗ₜ[R] x.2 i j) := by
  classical
  simp only [tensorCorrectionTarget, LinearEquiv.trans_apply, prodRight_tmul,
    LinearEquiv.prodCongr_apply, piRight_apply, piRightHom_tmul,
    ]
  apply Prod.ext rfl
  funext i j
  rfl

/-- The scalar coordinate is exactly the original tensor multiplier. -/
theorem tensorCorrectionCoordinates_fst (x : S ⊗[R] (R × ∀ i, A i)) :
    (tensorCorrectionCoordinates (A := A) S x).1 =
      tensorCorrectionMultiplier (A := A) S x := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => rw [tensorCorrectionCoordinates_tmul, tensorCorrectionMultiplier_tmul]
  | add x y hx hy => simp only [map_add, Prod.fst_add, hx, hy]

variable (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)

/-- Tensoring the full system gives exactly the independently extended original equations. -/
theorem tensorCorrectionSystem_coordinates (x : S ⊗[R] (R × ∀ i, A i)) :
    tensorCorrectionTarget (B := B) (C := C) S
      ((correctionSystem φ p q u).lTensor S x) =
    (fun i ↦ (φ i).toLinearMap.lTensor S ((tensorCorrectionCoordinates (A := A) S x).2 i),
      fun i j ↦
        (p i j).toLinearMap.lTensor S ((tensorCorrectionCoordinates (A := A) S x).2 i) -
        (q i j).toLinearMap.lTensor S ((tensorCorrectionCoordinates (A := A) S x).2 j) -
        (tensorCorrectionCoordinates (A := A) S x).1 ⊗ₜ[R]
          (p i j (u i) - q i j (u j))) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
      rw [LinearMap.lTensor_tmul, tensorCorrectionTarget_tmul,
        tensorCorrectionCoordinates_tmul]
      apply Prod.ext
      · rfl
      · funext i j
        change s ⊗ₜ[R] (p i j (x.2 i) - q i j (x.2 j) -
          p i j (algebraMap R (A i) x.1) * (p i j (u i) - q i j (u j))) = _
        simp only [AlgHom.commutes, tmul_sub, LinearMap.lTensor_tmul,
          AlgHom.toLinearMap_apply]
        congr 1
        simpa only [Algebra.smul_def, tmul_sub] using
          (TensorProduct.smul_tmul (R := R) x.1 s
          (p i j (u i) - q i j (u j))).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul]
      apply Prod.ext
      · rfl
      · funext i j
        simp only [Prod.snd_add, Pi.add_apply]
        abel

/-- Vanishing of the tensor system is exactly the original boundary and mixed equations. -/
theorem tensorCorrectionSystem_eq_zero_iff (x : S ⊗[R] (R × ∀ i, A i)) :
    (correctionSystem φ p q u).lTensor S x = 0 ↔
      (∀ i, (φ i).toLinearMap.lTensor S
        ((tensorCorrectionCoordinates (A := A) S x).2 i) = 0) ∧
      ∀ i j, (p i j).toLinearMap.lTensor S
          ((tensorCorrectionCoordinates (A := A) S x).2 i) -
        (q i j).toLinearMap.lTensor S ((tensorCorrectionCoordinates (A := A) S x).2 j) =
        (tensorCorrectionCoordinates (A := A) S x).1 ⊗ₜ[R]
          (p i j (u i) - q i j (u j)) := by
  rw [← (tensorCorrectionTarget (B := B) (C := C) S).map_eq_zero_iff,
    tensorCorrectionSystem_coordinates]
  change (_, _) = (0, 0) ↔ _
  simp only [Prod.mk.injEq, funext_iff, Pi.zero_apply, sub_eq_zero]

end FLT.Mazur.BoundaryCorrectionIdeal
