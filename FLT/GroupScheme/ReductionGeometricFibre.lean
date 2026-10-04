/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SurjectiveReductionBaseChange

/-! # Fibres of a presented reduction over the quotient base

The comparison works over every quotient-base algebra, with no flatness
hypothesis. Nilpotence is needed only to ensure all geometric points of
the original base factor through that quotient.
-/

@[expose] public noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct
namespace AlgHom
variable {B C D E Ω : Type*} [CommRing B] [CommRing C] [CommRing D] [CommRing E]
  [Algebra B C] [Algebra B D] [Algebra B E] [Algebra C E] [IsScalarTower B C E]
  (hq : Function.Surjective (algebraMap B C)) (t : D →ₐ[B] E)
  (ht : Function.Surjective t)
  (hker : RingHom.ker t = (RingHom.ker (algebraMap B C)).map (algebraMap B D))

/-- The original tensor reduction is an equivalence over the quotient base. -/
def reductionBaseChangeEquivOverQuotient : C ⊗[B] D ≃ₐ[C] E := by
  let e := (Algebra.TensorProduct.comm B C D).trans
    (reductionBaseChangeEquiv hq t ht hker)
  exact { e.toRingEquiv with
    commutes' := fun c ↦ by
      obtain ⟨b, rfl⟩ := hq c
      change e (algebraMap C (C ⊗[B] D) (algebraMap B C b)) =
        algebraMap C E (algebraMap B C b)
      rw [← IsScalarTower.algebraMap_apply B C E,
        ← IsScalarTower.algebraMap_apply B C (C ⊗[B] D)]
      exact e.commutes b }

/-- The quotient-base equivalence retains the specified reduction map. -/
@[simp]
theorem reductionBaseChangeEquivOverQuotient_one_tmul (d : D) :
    reductionBaseChangeEquivOverQuotient hq t ht hker (1 ⊗ₜ[B] d) = t d :=
  reductionBaseChangeEquiv_tmul_one hq t ht hker d

variable [CommRing Ω] [Algebra B Ω] [Algebra C Ω] [IsScalarTower B C Ω]

/-- Passing to any geometric point of the quotient identifies the two actual fibres. -/
def reductionFibreEquiv : Ω ⊗[B] D ≃ₐ[Ω] Ω ⊗[C] E :=
  (cancelBaseChange B C Ω Ω D).symm.trans
    (congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω)
      (reductionBaseChangeEquivOverQuotient hq t ht hker))

/-- The fibre comparison takes a lifted coordinate to its specified reduction. -/
@[simp]
theorem reductionFibreEquiv_tmul (s : Ω) (d : D) :
    reductionFibreEquiv hq t ht hker (s ⊗ₜ[B] d) = s ⊗ₜ[C] t d := by
  simp only [reductionFibreEquiv, AlgEquiv.trans_apply, cancelBaseChange_symm_tmul,
    congr_apply, map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply]
  change s ⊗ₜ[C] reductionBaseChangeEquivOverQuotient hq t ht hker (1 ⊗ₜ[B] d) = _
  rw [reductionBaseChangeEquivOverQuotient_one_tmul]

end AlgHom
