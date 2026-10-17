/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionOperatorIndependence
public import FLT.Mazur.CompatibleErrorBaseChange

/-!
# Compatible boundary errors over the actual local scalar algebras

Scalar extension preserves the correction image and the scalar error inside
the constructed compatible subspace. Its cokernel image is exactly the image
of the extended mixed boundary errors. Finite relative generators and residual
surjectivity onto this subspace suffice; neither is assumed for the full target.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  (J : ∀ i j, Ideal (C i j)) (S : Type*) [CommRing S] [Algebra R S]
set_option quotPrecheck false
local notation "F" => ambientCorrectionOperator φ p q u S
local notation "H" => (compatibleErrorSubspace φ p q u J).baseChange S
local notation "π" => (LinearMap.range F).mkQ

/-- Scalar extension retains the complete correction image in the compatible subspace. -/
theorem ambientCorrection_range_le_compatible : LinearMap.range F ≤ H := by
  rw [ambientCorrectionOperator_eq_baseChange, CompatibleErrorBaseChange.range_baseChange]
  exact Submodule.baseChange_mono S (correction_range_le_compatible φ p q u J)

/-- Exact mixed boundary membership puts the actual tensor scalar error in this subspace. -/
theorem ambientScalarError_mem_compatible
    (hu : ∀ i j, p i j (u i) - q i j (u j) ∈ J i j) :
    ambientScalarError φ p q u S ∈ H := by
  rw [ambientScalarError_eq_tmul]
  exact Submodule.tmul_mem_baseChange_of_mem 1 (scalarError_mem_compatible φ p q u J hu)

/-- The same scalar error lies in the compatible subspace defined with any reference lifts. -/
theorem ambientScalarError_mem_reference (v : ∀ i, A i)
    (hu : ∀ i j, p i j (u i) - q i j (u j) ∈ J i j) :
    ambientScalarError φ p q u S ∈ (compatibleErrorSubspace φ p q v J).baseChange S := by
  have h := ambientScalarError_mem_compatible φ p q u J S hu
  rwa [compatibleErrorSubspace_independent φ p q u v J] at h

/-- In the full ambient cokernel the constructed subspace is precisely the mixed-error image. -/
theorem ambientCompatible_map_cokernel :
    (H).map π = ((mixedBoundaryErrors (R := R) (B := B) J).baseChange S).map π := by
  rw [compatibleErrorSubspace, CompatibleErrorBaseChange.sup_baseChange,
    ← CompatibleErrorBaseChange.range_baseChange, ← ambientCorrectionOperator_eq_baseChange,
    Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]

/-- Finite generators modulo corrections and residual reduction construct finite cokernel data. -/
theorem compatible_exists_finite_cokernel (I : Ideal S)
    (E : Submodule S (S ⊗[R] ((∀ i, B i) × ∀ i j, C i j))) (hE : E.FG)
    (hgen : LinearMap.range F ⊔ E = H) (hres : LinearMap.range F ⊔ I • H = H)
    (hu : ∀ i j, p i j (u i) - q i j (u j) ∈ J i j) :
    ∃ Q : Submodule S ((S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)) ⧸ LinearMap.range F),
      Q.FG ∧ Q ≤ I • Q ∧ π (ambientScalarError φ p q u S) ∈ Q :=
  ⟨(H).map π, FiniteErrorReduction.cokernel_image_fg F H E hE hgen,
    FiniteErrorReduction.cokernel_image_le_smul F I H hres,
    Submodule.mem_map_of_mem (ambientScalarError_mem_compatible φ p q u J S hu)⟩

end FLT.Mazur.BoundaryCorrectionIdeal

namespace FLT.Mazur.FiniteErrorReduction
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Transport finite cokernel data along equality of full correction operators. -/
theorem finite_cokernel_of_operator_eq (F G : M →ₗ[R] N) (h : F = G)
    (I : Ideal R) (y : N) (Q : Submodule R (N ⧸ LinearMap.range G))
    (hQ : Q.FG) (hred : Q ≤ I • Q) (hy : (LinearMap.range G).mkQ y ∈ Q) :
    ∃ E : Submodule R (N ⧸ LinearMap.range F),
      E.FG ∧ E ≤ I • E ∧ (LinearMap.range F).mkQ y ∈ E := by
  subst G
  exact ⟨Q, hQ, hred, hy⟩

end FLT.Mazur.FiniteErrorReduction
