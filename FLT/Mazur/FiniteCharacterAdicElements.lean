/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompleteAffinePoints
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Effective finite-character coefficients over the original complete base

For a finite character group, compatible quotient coefficients reconstruct an
element of the original character algebra. No Noetherian hypothesis or change
of the complete base ring is needed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteCharacterAdicElements

variable {R G : Type} [CommRing R] [AddCommMonoid G] (I : Ideal R)

/-- The original coefficient reduction on the whole character algebra. -/
def reduction (m : ℕ) : AddMonoidAlgebra R G →+* AddMonoidAlgebra (R ⧸ I ^ (m + 1)) G :=
  AddMonoidAlgebra.mapRingHom G (Ideal.Quotient.mk _)

/-- The full adjacent restriction of character coefficients. -/
def restriction (m : ℕ) : AddMonoidAlgebra (R ⧸ I ^ (m + 2)) G →+*
    AddMonoidAlgebra (R ⧸ I ^ (m + 1)) G :=
  AddMonoidAlgebra.mapRingHom G
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))))

variable (x : ∀ m : ℕ, AddMonoidAlgebra (R ⧸ I ^ (m + 1)) G)
  (hx : ∀ m, restriction I m (x (m + 1)) = x m)

include hx in
/-- Adjacent compatibility retains each coefficient at every earlier positive order. -/
theorem coefficient_compatible (a : G) {m n : ℕ} (hmn : m ≤ n) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))
      ((x n).coeff a) = (x m).coeff a := by
  induction n, hmn using Nat.le_induction with
  | base => simp only [Ideal.Quotient.factor_eq, RingHom.id_apply]
  | succ n hmn ih =>
    rw [← Ideal.Quotient.factor_comp_apply
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))]
    have h := congrArg (fun z => z.coeff a) (hx n)
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      ((x (n + 1)).coeff a) = (x n).coeff a at h
    rw [h, ih]

/-- The compatible positive-order section of one original character coefficient. -/
def coefficientSection (a : G) : AdicCompletionPositiveLimit.sections I :=
  ⟨fun m => (x m).coeff a, fun hmn => coefficient_compatible I x hx a hmn⟩

variable [IsAdicComplete I R]

/-- The actual coefficient in the original complete base ring. -/
def coefficientLift (a : G) : R :=
  (AdicCompletion.ofAlgEquiv I).symm
    (AdicCompletionPositiveLimit.fromSections I (coefficientSection I x hx a))

/-- Each reconstructed coefficient retains all its prescribed quotient values. -/
theorem coefficientLift_reduction (a : G) (m : ℕ) :
    Ideal.Quotient.mk (I ^ (m + 1)) (coefficientLift I x hx a) = (x m).coeff a := by
  rw [coefficientLift, AdicCompletion.mk_ofAlgEquiv_symm,
    AdicCompletionPositiveLimit.eval_fromSections]
  rfl

/-- All original coefficient reductions detect equality in the entire character algebra. -/
theorem reduction_ext {p q : AddMonoidAlgebra R G}
    (h : ∀ m, reduction I m p = reduction I m q) : p = q := by
  ext a
  apply AdicCompleteAffinePoints.element_ext I
  intro m
  exact congrArg (fun z => z.coeff a) (h m)

variable [Finite G]

/-- Finite support is automatic for a finite character group, giving an actual algebra element. -/
def lift : AddMonoidAlgebra R G :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (coefficientLift I x hx))

/-- The reconstructed original algebra element has exactly the specified finite reductions. -/
theorem reduction_lift (m : ℕ) : reduction I m (lift I x hx) = x m := by
  ext a
  exact coefficientLift_reduction I x hx a m

/-- The finite coefficient data uniquely determine the element over the original complete base. -/
theorem lift_unique (p : AddMonoidAlgebra R G) (hp : ∀ m, reduction I m p = x m) :
    p = lift I x hx := by
  apply reduction_ext I
  intro m
  rw [hp, reduction_lift]

end FLT.Mazur.FiniteCharacterAdicElements
