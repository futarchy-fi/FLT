/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionCokernelBaseChange
public import FLT.Mazur.PairedCokernelReduction

/-!
# The full correction cokernel as a mixed-discrepancy quotient

Surjectivity of the chart boundary maps eliminates their coordinate block.
The surviving quotient retains every mixed equation and divides only by
mixed discrepancies of families in the exact boundary kernels.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)

/-- All original boundary coordinates. -/
def boundaryCoordinates : (∀ i, A i) →ₗ[R] (∀ i, B i) :=
  LinearMap.pi fun i ↦ (φ i).toLinearMap.comp (LinearMap.proj i)

/-- All independent mixed discrepancies, with no restriction to a chosen common frame. -/
def mixedDiscrepancy : (∀ i, A i) →ₗ[R] (∀ i j, C i j) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (p i j).toLinearMap.comp (LinearMap.proj i) -
      (q i j).toLinearMap.comp (LinearMap.proj j)

/-- The removable mixed discrepancies come from exact boundary-kernel families. -/
def mixedCorrectionImage : Submodule R (∀ i j, C i j) :=
  (LinearMap.ker (boundaryCoordinates φ)).map (mixedDiscrepancy p q)

/-- The fixed original operator is precisely the pair of these two blocks. -/
theorem originalCorrectionOperator_eq_prod :
    originalCorrectionOperator φ p q 0 = (boundaryCoordinates φ).prod (mixedDiscrepancy p q) := by
  apply LinearMap.ext
  intro a
  exact originalCorrectionOperator_apply φ p q 0 a

/-- Chartwise boundary lifts assemble into a surjective boundary block. -/
theorem boundaryCoordinates_surjective (hφ : ∀ i, Function.Surjective (φ i)) :
    Function.Surjective (boundaryCoordinates φ) := by
  intro v
  choose u hu using fun i ↦ hφ i (v i)
  exact ⟨u, funext hu⟩

/-- The mixed quotient maps isomorphically to the full unchanged correction cokernel. -/
def mixedCokernelEquiv (hφ : ∀ i, Function.Surjective (φ i)) :
    ((∀ i j, C i j) ⧸ mixedCorrectionImage φ p q) ≃ₗ[R]
      (((∀ i, B i) × ∀ i j, C i j) ⧸
        LinearMap.range (originalCorrectionOperator φ p q 0)) :=
  (PairedCokernel.equiv (boundaryCoordinates φ) (mixedDiscrepancy p q)
    (boundaryCoordinates_surjective φ hφ)).trans
      (Submodule.quotEquivOfEq _ _
        (congrArg LinearMap.range (originalCorrectionOperator_eq_prod φ p q)).symm)

/-- The isomorphism inserts a mixed representative with boundary coordinate zero. -/
theorem mixedCokernelEquiv_mk (hφ : ∀ i, Function.Surjective (φ i))
    (v : ∀ i j, C i j) :
    mixedCokernelEquiv φ p q hφ ((mixedCorrectionImage φ p q).mkQ v) =
      (LinearMap.range (originalCorrectionOperator φ p q 0)).mkQ (0, v) := rfl

/-- An actual boundary lift represents its class by its negative full mixed discrepancy. -/
theorem mixedCokernelEquiv_boundary (hφ : ∀ i, Function.Surjective (φ i)) (u : ∀ i, A i) :
    mixedCokernelEquiv φ p q hφ
        ((mixedCorrectionImage φ p q).mkQ (-mixedDiscrepancy p q u)) =
      (LinearMap.range (originalCorrectionOperator φ p q 0)).mkQ
        (boundaryCoordinates φ u, 0) := by
  rw [mixedCokernelEquiv_mk]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-u, ?_⟩
  rw [originalCorrectionOperator_eq_prod]
  apply Prod.ext
  · change boundaryCoordinates φ (-u) = 0 - boundaryCoordinates φ u
    rw [map_neg, zero_sub]
  · change mixedDiscrepancy p q (-u) = -mixedDiscrepancy p q u - 0
    rw [map_neg, sub_zero]

/-- Vanishing in the full cokernel is exactly a simultaneous correction in the boundary kernels. -/
theorem scalarError_eq_zero_iff_mixed (u : ∀ i, A i) :
    (LinearMap.range (originalCorrectionOperator φ p q 0)).mkQ
        (correctionSystem φ p q u (1, 0)) = 0 ↔
      mixedDiscrepancy p q u ∈ mixedCorrectionImage φ p q := by
  rw [scalarError_cokernel_eq_boundary φ p q u 0, originalCorrectionOperator_eq_prod]
  exact PairedCokernel.boundary_eq_zero_iff (boundaryCoordinates φ) (mixedDiscrepancy p q) u

/-- Residual scalar errors are tested by genuine boundary-kernel corrections. -/
theorem scalarError_mem_smul_top_iff_mixed (hφ : ∀ i, Function.Surjective (φ i))
    (J : Ideal R) (u : ∀ i, A i) :
    (LinearMap.range (originalCorrectionOperator φ p q 0)).mkQ
        (correctionSystem φ p q u (1, 0)) ∈
          J • (⊤ : Submodule R (((∀ i, B i) × ∀ i j, C i j) ⧸
            LinearMap.range (originalCorrectionOperator φ p q 0))) ↔
      ∃ z : ∀ i, A i, boundaryCoordinates φ z = 0 ∧
        mixedDiscrepancy p q u - mixedDiscrepancy p q z ∈
          J • (⊤ : Submodule R (∀ i j, C i j)) := by
  rw [scalarError_cokernel_eq_boundary φ p q u 0, originalCorrectionOperator_eq_prod]
  exact PairedCokernel.boundary_mem_smul_top_iff_correction
    (boundaryCoordinates φ) (mixedDiscrepancy p q) (boundaryCoordinates_surjective φ hφ) J u

end FLT.Mazur.BoundaryCorrectionIdeal
