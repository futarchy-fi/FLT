/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SubmoduleQuotientScalarReduction
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Quotient presentations for scalar extension followed by reduction

The residue ideal belongs to the new scalar ring. Its multiples are taken
inside the extended module, after extending the original correction module.
No flatness of either scalar extension or residue algebra is used here.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarQuotientResiduePresentation
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (K : Submodule R M)

/-- Quotienting by the extended correction image presents the extended original quotient. -/
def quotientEquiv : S ⊗[R] (M ⧸ K) ≃ₗ[S] (S ⊗[R] M) ⧸ K.baseChange S :=
  AlgebraTensorModule.tensorQuotientEquiv S R S K

/-- The presentation preserves the original numerator and its new scalar coefficient. -/
theorem quotientEquiv_tmul (s : S) (x : M) :
    quotientEquiv S K (s ⊗ₜ[R] K.mkQ x) = (K.baseChange S).mkQ (s ⊗ₜ[R] x) := rfl

/-- Reduction after extension uses the new residue ideal and the extended original corrections. -/
theorem residue_mk_eq_zero_iff (J : Ideal S) (x : M) :
    (1 ⊗ₜ[S] (1 ⊗ₜ[R] K.mkQ x) : (S ⧸ J) ⊗[S] (S ⊗[R] (M ⧸ K))) = 0 ↔
      (1 ⊗ₜ[R] x : S ⊗[R] M) ∈ K.baseChange S ⊔ J • (⊤ : Submodule S (S ⊗[R] M)) := by
  rw [← ((quotientEquiv S K).lTensor (S ⧸ J)).map_eq_zero_iff]
  change (1 ⊗ₜ[S] (K.baseChange S).mkQ (1 ⊗ₜ[R] x) :
    (S ⧸ J) ⊗[S] ((S ⊗[R] M) ⧸ K.baseChange S)) = 0 ↔ _
  exact RelativeSubmoduleQuotient.residue_mk_eq_zero_iff J (K.baseChange S) _

end FLT.Mazur.ScalarQuotientResiduePresentation
