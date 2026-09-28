/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD

/-!
# Integral coordinate evaluations in the full point field

Every generic coordinate value belongs to the field cut out by the full point
action. Restricting evaluation to a finite-flat integral model still separates
its geometric points.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan
namespace FiniteContinuousGaloisModule

/-- Every generic coordinate value is fixed by the full point-action kernel. -/
theorem genericCoordinate_mem_pointField (W : FiniteContinuousGaloisModule)
    (a : W.GenericCoordinateAlgebra) (w : W) : a w ∈ W.pointField := by
  rw [pointField, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  change σ • a w = a w
  rw [← map_smul, (W.mem_pointActionKernel σ).mp hσ w]

/-- Evaluation of generic coordinates takes values in the full point field. -/
def pointFieldEval (W : FiniteContinuousGaloisModule) (w : W) :
    W.GenericCoordinateAlgebra →ₐ[ℚ] W.pointField :=
  (MulActionHom.evalAlgHom (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    ℚ W (AlgebraicClosure ℚ) w).codRestrict W.pointField.toSubalgebra
    (fun a ↦ W.genericCoordinate_mem_pointField a w)

end FiniteContinuousGaloisModule

namespace HasFiniteFlatModel

variable {R : Type} [CommRing R] [Algebra R ℚ] {W : FiniteContinuousGaloisModule}
  (M : HasFiniteFlatModel R W)

/-- An integral model coordinate evaluates in the point field. -/
def pointFieldPoint (w : W) : M.CoordinateRing →ₐ[R] W.pointField :=
  (((W.pointFieldEval w).comp M.genericBialgEquiv.symm.toAlgEquiv.toAlgHom).restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- Integral-coordinate evaluation respects the full Galois action. -/
theorem pointFieldPoint_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : W) (a : M.CoordinateRing) :
    M.pointFieldPoint (σ • w) a =
      AlgEquiv.restrictNormalHom W.pointField σ (M.pointFieldPoint w a) := by
  apply Subtype.ext
  change (M.genericBialgEquiv.symm (1 ⊗ₜ[R] a)) (σ • w) = _
  rw [map_smul]
  exact (AlgEquiv.restrictNormalHom_apply W.pointField σ (M.pointFieldPoint w a)).symm

/-- Restricting generic evaluation to integral model coordinates still separates points. -/
theorem pointFieldPoint_injective : Function.Injective M.pointFieldPoint := by
  intro x y h
  apply (InfiniteGalois.evalAlgHom_bijective ℚ (AlgebraicClosure ℚ) W).1
  have he : ((W.pointFieldEval x).comp M.genericBialgEquiv.symm.toAlgEquiv.toAlgHom) =
      ((W.pointFieldEval y).comp M.genericBialgEquiv.symm.toAlgEquiv.toAlgHom) := by
    exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) h
  ext a
  have ha := AlgHom.congr_fun he (M.genericBialgEquiv a)
  change W.pointFieldEval x (M.genericBialgEquiv.symm (M.genericBialgEquiv a)) =
    W.pointFieldEval y (M.genericBialgEquiv.symm (M.genericBialgEquiv a)) at ha
  rw [M.genericBialgEquiv.symm_apply_apply] at ha
  exact congrArg Subtype.val ha

end HasFiniteFlatModel
end ThreeAdicPlan
