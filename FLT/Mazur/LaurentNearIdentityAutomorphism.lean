/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentNilpotentReparametrization

/-!
# Full Laurent automorphisms near the positive coordinate

A nilpotent coefficient perturbation of the positive coordinate acts invertibly
on every Laurent polynomial. Both directions are congruent to the identity.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentNearIdentityAutomorphism
open LaurentPolynomial LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]
variable (I : Ideal R) (hI : IsNilpotent I) (u : R[T;T⁻¹]ˣ)
  (hu : (u : R[T;T⁻¹]) - T 1 ∈ I.map (algebraMap R R[T;T⁻¹]))

include hu in
/-- A coordinate congruence controls the entire substitution, including negative powers. -/
theorem eval_sub_mem (x : R[T;T⁻¹]) : evalUnit u x - x ∈ I.map (algebraMap R R[T;T⁻¹]) := by
  apply LaurentNilpotentReparametrization.hom_sub_mem _ (evalUnit u) (AlgHom.id R R[T;T⁻¹])
  simpa only [evalUnit_T, zpow_one, AlgHom.id_apply] using hu

/-- Finite nilpotent contraction constructs the full inverse substitution. -/
def equiv : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹] :=
  NilpotentAlgebraAutomorphism.equiv I (evalUnit u) (eval_sub_mem I u hu) hI

/-- The forward map evaluates at the exact original unit. -/
theorem equiv_toAlgHom : (equiv I hI u hu).toAlgHom = evalUnit u := rfl

/-- The positive coordinate retains every coefficient of the original unit. -/
theorem equiv_T : equiv I hI u hu (T 1) = (u : R[T;T⁻¹]) := by
  change evalUnit u (T 1) = _
  rw [evalUnit_T, zpow_one]

/-- The inverse preserves the same coefficient congruence on every Laurent function. -/
theorem symm_sub_mem (x : R[T;T⁻¹]) :
    (equiv I hI u hu).symm x - x ∈ I.map (algebraMap R R[T;T⁻¹]) := by
  have h := (I.map (algebraMap R R[T;T⁻¹])).neg_mem
    (eval_sub_mem I u hu ((equiv I hI u hu).symm x))
  change -(equiv I hI u hu ((equiv I hI u hu).symm x) - _) ∈ _ at h
  simpa only [AlgEquiv.apply_symm_apply, neg_sub] using h

end FLT.Mazur.LaurentNearIdentityAutomorphism
