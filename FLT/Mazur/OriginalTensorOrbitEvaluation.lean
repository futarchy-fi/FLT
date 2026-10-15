/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranscendentalCoefficientOrbitAvoidance

/-!
# Transcendental coefficient reduction on the original affine algebra

Cancel the intermediate algebraic scalar extension and retain functions on
K tensor_k A itself. Evaluation at a conjugate of an algebraic A-point agrees
with the iterated-tensor evaluation used in coefficient detection.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
open scoped TensorProduct
open TensorCoefficientDetection AlgebraicTensorCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
variable {k L K A : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [CommRing A] [Algebra k A]

/-- Evaluate the original affine coordinates in the unchanged larger field. -/
def originalEvaluation (q : A →ₐ[k] L) (σ : L ≃ₐ[k] L) : K ⊗[k] A →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K)
    ((IsScalarTower.toAlgHom k L K).comp (σ.toAlgHom.comp q))
    (fun _ _ ↦ Commute.all _ _)

/-- The actual larger-field evaluation on pure tensors. -/
@[simp]
theorem originalEvaluation_tmul (q : A →ₐ[k] L) (σ : L ≃ₐ[k] L) (z : K) (a : A) :
    originalEvaluation (K := K) q σ (z ⊗ₜ[k] a) = z * algebraMap L K (σ (q a)) := rfl

/-- Cancelling the intermediate tensor factor preserves whole evaluations. -/
theorem evaluation_cancel (p : L ⊗[k] A →ₐ[L] L) (σ : L ≃ₐ[k] L) (x : K ⊗[k] A) :
    evaluation (K := K) (conjugatePoint p σ)
      ((Algebra.TensorProduct.cancelBaseChange k L K K A).symm x) =
        originalEvaluation ((p.restrictScalars k).comp Algebra.TensorProduct.includeRight) σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul z a =>
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, evaluation_tmul,
      conjugatePoint_tmul, one_mul, originalEvaluation_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Finitely many actual original functions have one whole algebraic point orbit avoiding them. -/
theorem exists_original_point_all_conjugates
    [Algebra.IsAlgebraic k L] [IsAlgClosed L] [Algebra.FiniteType k A]
    [IsDomain (L ⊗[k] A)] {J : Type*} [Finite J]
    (x : J → K ⊗[k] A) (hx : ∀ j, x j ≠ 0) :
    ∃ q : A →ₐ[k] L, ∀ (σ : L ≃ₐ[k] L) (j : J),
      originalEvaluation (K := K) q σ (x j) ≠ 0 := by
  let e := Algebra.TensorProduct.cancelBaseChange k L K K A
  obtain ⟨p, hp⟩ := exists_point_all_conjugates (fun j ↦ e.symm (x j))
    (fun j h ↦ hx j (e.symm.injective (h.trans (map_zero _).symm)))
  refine ⟨(p.restrictScalars k).comp Algebra.TensorProduct.includeRight, fun σ j ↦ ?_⟩
  rw [← evaluation_cancel]
  exact hp σ j

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
