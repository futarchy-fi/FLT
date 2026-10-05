/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelHomTransport

/-!
# Models of presentations obtained by scalar extension

A presentation over an integer coefficient subring gives a presentation of
any identified scalar extension. Its coefficient model at the original
stage recovers the given algebra, with the specified recovery map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
  (A₀ : Subalgebra ℤ A) {C₀ : Type u} [CommRing C₀] [Algebra A₀ C₀]
  {n m : ℕ} (Q₀ : Algebra.Presentation A₀ C₀ (Fin n) (Fin m))
  (e : A ⊗[A₀] C₀ ≃ₐ[A] C)

/-- The presentation of an identified scalar extension induced by an old presentation. -/
def integerBaseChangedPresentation : Algebra.Presentation A C (Fin n) (Fin m) :=
  (Q₀.baseChange A).ofAlgEquiv e

instance integerBaseChangedPresentation_hasCoeffs :
    (integerBaseChangedPresentation A₀ Q₀ e).HasCoeffs A₀ := by
  constructor
  rintro a ⟨_, ⟨j, rfl⟩, ha⟩
  exact mem_range_map_iff_coeffs_subset.mp ⟨Q₀.relation j, rfl⟩ ha

/-- The selected relation lifts are exactly the original relations. -/
@[simp]
theorem integerBaseChangedPresentation_relation (j : Fin m) :
    (integerBaseChangedPresentation A₀ Q₀ e).relationOfHasCoeffs A₀ j =
      Q₀.relation j := by
  apply MvPolynomial.map_injective (f := algebraMap A₀ A) Subtype.val_injective
  exact (integerBaseChangedPresentation A₀ Q₀ e).map_relationOfHasCoeffs A₀ j

/-- At the original coefficient stage the new presentation models the old algebra. -/
def integerBaseChangedModelEquiv :
    (integerBaseChangedPresentation A₀ Q₀ e).ModelOfHasCoeffs A₀ ≃ₐ[A₀] C₀ :=
  by
  have heq : (integerBaseChangedPresentation A₀ Q₀ e).relationOfHasCoeffs A₀ =
      Q₀.relation := funext (integerBaseChangedPresentation_relation A₀ Q₀ e)
  have hid : Ideal.span (Set.range
      ((integerBaseChangedPresentation A₀ Q₀ e).relationOfHasCoeffs A₀)) = Q₀.ker := by
    rw [heq]
    exact Q₀.span_range_relation_eq_ker
  exact (Ideal.quotientEquivAlgOfEq A₀ hid).trans (Q₀.quotientEquiv.restrictScalars A₀)

/-- The model identification evaluates polynomial representatives in the old algebra. -/
@[simp]
theorem integerBaseChangedModelEquiv_mk (p : MvPolynomial (Fin n) A₀) :
    integerBaseChangedModelEquiv A₀ Q₀ e (Ideal.Quotient.mk _ p) = aeval Q₀.val p := by
  simp [integerBaseChangedModelEquiv, Q₀.quotientEquiv_mk, Q₀.algebraMap_apply]

/-- The model identification retains the specified recovery into the scalar extension. -/
theorem integerBaseChangedModelEquiv_recovery
    (b : (integerBaseChangedPresentation A₀ Q₀ e).ModelOfHasCoeffs A₀) :
    (integerBaseChangedPresentation A₀ Q₀ e).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b) =
      e (1 ⊗ₜ integerBaseChangedModelEquiv A₀ Q₀ e b) := by
  induction b using Quotient.inductionOn' with | _ p => ?_
  change (integerBaseChangedPresentation A₀ Q₀ e).tensorModelOfHasCoeffsEquiv A₀
    (1 ⊗ₜ Ideal.Quotient.mk _ p) =
      e (1 ⊗ₜ integerBaseChangedModelEquiv A₀ Q₀ e (Ideal.Quotient.mk _ p))
  rw [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
    integerBaseChangedModelEquiv_mk]
  let f : C₀ →ₐ[A₀] C := (e.toAlgHom.restrictScalars A₀).comp
    Algebra.TensorProduct.includeRight
  change aeval (fun i ↦ f (Q₀.val i)) p = f (aeval Q₀.val p)
  exact (MvPolynomial.comp_aeval_apply Q₀.val f p).symm

end FLT.Mazur.Approximation
