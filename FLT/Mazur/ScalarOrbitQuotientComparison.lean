/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarOrbitFiniteEquations

/-!
# Exact quotient and scalar fullness for the original orbit comparison

The full orbit algebra is the quotient by the constructed balancing ideal.
Actual scalar-image fullness kills that ideal and recovers an isomorphism
over the original ring, which is allowed to have a kernel in the source.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarOrbitTensorComparison
open FiniteGroupQuotient
variable (G R A : Type*) [Group G] [CommRing R] [CommRing A]
  [MulSemiringAction G A] [Algebra R A] [Algebra R (invariantRing G A)]
  [IsScalarTower R (invariantRing G A) A]
local notation "S" => invariantRing G A
local notation "C" => A ⊗[R] A

/-- Full scalar-image membership kills every invariant balancing equation. -/
theorem balancingIdeal_eq_bot_of_full
    (hfull : Function.Surjective (algebraMap R S)) : balancingIdeal G R A = ⊥ := by
  apply bot_unique
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  obtain ⟨r, rfl⟩ := hfull s
  change (algebraMap R S r).val ⊗ₜ[R] (1 : A) -
    (1 ⊗ₜ[R] (algebraMap R S r).val) = 0
  have hr : (algebraMap R S r).val = algebraMap R A r :=
    (IsScalarTower.algebraMap_apply R S A r).symm
  rw [hr]
  apply sub_eq_zero.mpr
  simpa only [Algebra.smul_def, mul_one] using
    (TensorProduct.smul_tmul (R := R) r (1 : A) (1 : A))

variable [Finite G] (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)

/-- The original orbit algebra is the full quotient by precisely the balancing ideal. -/
def quotientComparison : (C ⧸ balancingIdeal G R A) ≃ₐ[R] (G → A) :=
  (Ideal.quotientEquivAlgOfEq R
    (comparison_ker_eq_balancingIdeal G R A hfree).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (comparison_surjective G R A hfree))

/-- The quotient isomorphism retains every original coordinate evaluation. -/
theorem quotientComparison_mk (t : C) :
    quotientComparison G R A hfree (Ideal.Quotient.mk _ t) = comparison G R A t := rfl

/-- Exact scalar fullness upgrades the original comparison itself to an isomorphism. -/
def fullComparison (hfull : Function.Surjective (algebraMap R S)) : C ≃ₐ[R] (G → A) :=
  AlgEquiv.ofBijective (comparison G R A)
    ⟨(comparison_injective_iff G R A hfree).mpr
      (balancingIdeal_eq_bot_of_full G R A hfull), comparison_surjective G R A hfree⟩

/-- Both source factors remain unchanged in the constructed original-base isomorphism. -/
theorem fullComparison_tmul (hfull : Function.Surjective (algebraMap R S))
    (a b : A) (g : G) : fullComparison G R A hfree hfull (a ⊗ₜ[R] b) g = a * (g • b) :=
  rfl

end FLT.Mazur.ScalarOrbitTensorComparison
