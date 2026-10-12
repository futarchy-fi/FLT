/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocalizedAmbientTransition

/-!
# Identity ambient changes

The self-overlap determinant is one, and the rational transition is the
original polynomial algebra map. These are the algebraic self-gluing laws.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {d : ℕ}

omit [Fintype ι] in
/-- The selected identity block is the identity matrix. -/
@[simp] theorem ambientBlockP_refl :
    ambientBlockP (LinearMap.id : ((Fin d → R) × (ι → R)) →ₗ[R] _) = 1 := by
  classical
  ext i j
  simp [ambientBlockP, LinearMap.toMatrix'_apply, Matrix.one_apply, Pi.single_apply]

omit [Fintype ι] in
/-- The lower off-diagonal identity block is zero. -/
@[simp] theorem ambientBlockQ_refl :
    ambientBlockQ (LinearMap.id : ((Fin d → R) × (ι → R)) →ₗ[R] _) = 0 := by
  classical
  ext i j
  simp [ambientBlockQ, LinearMap.toMatrix'_apply]

/-- The upper off-diagonal identity block is zero. -/
@[simp] theorem ambientBlockU_refl :
    ambientBlockU (LinearMap.id : ((Fin d → R) × (ι → R)) →ₗ[R] _) = 0 := by
  classical
  ext i j
  simp [ambientBlockU, LinearMap.toMatrix'_apply]

/-- The complementary identity block is the identity matrix. -/
@[simp] theorem ambientBlockT_refl :
    let _ := Classical.decEq ι
    ambientBlockT (LinearMap.id : ((Fin d → R) × (ι → R)) →ₗ[R] _) = 1 := by
  classical
  ext i j
  simp [ambientBlockT, LinearMap.toMatrix'_apply, Matrix.one_apply, Pi.single_apply]

/-- The self-overlap polynomial is one, so the self-overlap is the whole chart. -/
theorem ambientOverlapPolynomial_refl :
    overlapPolynomial
      (ambientBlockP (LinearMap.id : ((Fin d → R) × (ι → R)) →ₗ[R] _))
      (ambientBlockQ (LinearMap.id : ((Fin d → R) × (ι → R)) →ₗ[R] _)) = 1 := by
  classical
  simp only [overlapPolynomial, ambientBlockP_refl, ambientBlockQ_refl]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]
  simp

/-- The identity ambient change fixes every matrix of quotient coordinates. -/
theorem ambientTransitionMatrix_refl (A : Matrix (Fin d) ι R) :
    ambientTransitionMatrix A (LinearEquiv.refl R _) = A := by
  classical
  simp [ambientTransitionMatrix, blockTransitionMatrix]

/-- Scalar extension carries the identity ambient equivalence to the identity. -/
theorem ambientEquivBaseChange_refl (S : Type*) [CommRing S] [Algebra R S] :
    ambientEquivBaseChange S (LinearEquiv.refl R ((Fin d → R) × (ι → R))) =
      LinearEquiv.refl S _ := by
  apply LinearEquiv.ext
  intro x
  simp only [ambientEquivBaseChange, LinearEquiv.trans_apply]
  change splitAmbientTensorEquiv S ι d
    ((LinearMap.id.baseChange S) ((splitAmbientTensorEquiv S ι d).symm x)) = x
  rw [LinearMap.baseChange_id, LinearMap.id_apply, LinearEquiv.apply_symm_apply]

/-- The self-transition of the universal polynomial chart is its localization map. -/
theorem ambientTransitionPolynomialHom_refl :
    ambientTransitionPolynomialHom (LinearEquiv.refl R ((Fin d → R) × (ι → R))) =
      Algebra.algHom R _ _ := by
  apply (matrixPolynomialHomEquiv R _ ι d).injective
  rw [ambientTransitionPolynomialHom_matrix, ambientEquivBaseChange_refl,
    ambientTransitionMatrix_refl]
  rfl

end FLT.Mazur.GrassmannianChart
