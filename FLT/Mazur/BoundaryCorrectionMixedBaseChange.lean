/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionMixedCokernel

/-!
# Mixed-discrepancy presentation after arbitrary scalar extension

Right exactness and boundary elimination identify the entire extended
correction cokernel with the tensor of the mixed quotient. This comparison
also applies to residue algebras; no flatness of those algebras is required.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
  (hφ : ∀ i, Function.Surjective (φ i)) (S : Type*) [CommRing S] [Algebra R S]
set_option quotPrecheck false
local notation "F" => ambientCorrectionOperator φ p q 0 S
local notation "K" => mixedCorrectionImage φ p q
local notation "N" => ((∀ i, B i) × ∀ i j, C i j)

/-- The full extended cokernel is exactly the scalar extension of the mixed quotient. -/
def ambientMixedCokernelEquiv :
    ((S ⊗[R] N) ⧸ LinearMap.range F) ≃ₗ[S] S ⊗[R] ((∀ i j, C i j) ⧸ K) :=
  (boundaryCokernelBaseChangeEquiv φ p q 0 S).trans
    ((mixedCokernelEquiv φ p q hφ).symm.baseChange R S _ _)

/-- Inserting a mixed tensor agrees with the full comparison. -/
theorem ambientMixedCokernelEquiv_mk_tmul (s : S) (v : ∀ i j, C i j) :
    ambientMixedCokernelEquiv φ p q hφ S
      ((LinearMap.range F).mkQ (s ⊗ₜ[R] (0, v))) = s ⊗ₜ[R] (K).mkQ v := by
  change ((mixedCokernelEquiv φ p q hφ).symm.baseChange R S _ _)
    (boundaryCokernelBaseChangeEquiv φ p q 0 S
      ((LinearMap.range F).mkQ (s ⊗ₜ[R] (0, v)))) = _
  rw [boundaryCokernelBaseChangeEquiv_mk_tmul, LinearEquiv.baseChange_tmul,
    ← mixedCokernelEquiv_mk φ p q hφ, LinearEquiv.symm_apply_apply]

/-- The actual scalar error becomes the negative full discrepancy class of its chosen lifts. -/
theorem ambientMixedCokernelEquiv_scalarError (u : ∀ i, A i) :
    ambientMixedCokernelEquiv φ p q hφ S
        ((LinearMap.range F).mkQ (ambientScalarError φ p q u S)) =
      1 ⊗ₜ[R] (K).mkQ (-mixedDiscrepancy p q u) := by
  rw [ambientScalarError_cokernel_eq_boundary φ p q u 0 S]
  change ((mixedCokernelEquiv φ p q hφ).symm.baseChange R S _ _)
    (boundaryCokernelBaseChangeEquiv φ p q 0 S
      ((LinearMap.range F).mkQ (1 ⊗ₜ[R] (boundaryCoordinates φ u, 0)))) = _
  rw [boundaryCokernelBaseChangeEquiv_mk_tmul, LinearEquiv.baseChange_tmul,
    ← mixedCokernelEquiv_boundary φ p q hφ, LinearEquiv.symm_apply_apply]

include hφ in
/-- Scalar-error vanishing is detected in the mixed quotient after any base change. -/
theorem ambientScalarError_eq_zero_iff_mixed (u : ∀ i, A i) :
    (LinearMap.range F).mkQ (ambientScalarError φ p q u S) = 0 ↔
      (1 ⊗ₜ[R] (K).mkQ (mixedDiscrepancy p q u) : S ⊗[R] ((∀ i j, C i j) ⧸ K)) = 0 := by
  rw [← (ambientMixedCokernelEquiv φ p q hφ S).map_eq_zero_iff,
    ambientMixedCokernelEquiv_scalarError, map_neg, tmul_neg, neg_eq_zero]

end FLT.Mazur.BoundaryCorrectionIdeal
