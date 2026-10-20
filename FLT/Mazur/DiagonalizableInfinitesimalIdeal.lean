/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableSquareZeroCoefficients

/-!
# The full infinitesimal ideal of a diagonalizable test scheme

The kernel of the actual coefficient reduction is identified with finitely
supported characters with coefficients in the original base ideal. If that
base ideal is square zero, so is the entire coordinate reduction kernel.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

variable (R G : Type*) [CommRing R] [AddCommMonoid G] (I : Ideal R)

/-- The kernel of the actual base reduction on the character coordinate algebra. -/
def coefficientIdeal : Ideal (AddMonoidAlgebra R G) :=
  RingHom.ker (AddMonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I))

/-- Membership retains every original coefficient, including infinitesimal ones. -/
theorem mem_coefficientIdeal (p : AddMonoidAlgebra R G) :
    p ∈ coefficientIdeal R G I ↔ InCoefficients I p :=
  (inCoefficients_iff_reduction I p).symm

/-- The whole coordinate kernel inherits square-zero multiplication from the base. -/
theorem coefficientIdeal_sq_zero (hI : I ^ 2 = ⊥) :
    coefficientIdeal R G I ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two, Ideal.mul_le]
  intro p hp q hq
  rw [Ideal.mem_bot]
  exact ((mem_coefficientIdeal R G I p).mp hp).mul_eq_zero I hI
    ((mem_coefficientIdeal R G I q).mp hq)

/-- Insert ideal-valued coefficients into the full original coordinate kernel. -/
def fromIdealCoefficients : (G →₀ I) →ₗ[R] coefficientIdeal R G I where
  toFun q := ⟨.ofCoeff (q.mapRange (fun a ↦ a.val) rfl),
    (mem_coefficientIdeal R G I _).mpr (fun a ↦ (q a).property)⟩
  map_add' x y := by
    apply Subtype.ext
    ext a
    rfl
  map_smul' r x := by
    apply Subtype.ext
    ext a
    rfl

/-- The insertion retains the original coefficient in the original ring. -/
theorem fromIdealCoefficients_coeff (q : G →₀ I) (a : G) :
    (fromIdealCoefficients R G I q).val.coeff a = (q a).val := rfl

/-- No coefficient information is lost when passing to the reduction kernel. -/
theorem fromIdealCoefficients_bijective :
    Function.Bijective (fromIdealCoefficients R G I) := by
  constructor
  · intro p q h
    ext a
    exact congrArg (fun x : coefficientIdeal R G I ↦ x.val.coeff a) h
  · intro p
    let q : G →₀ I :=
      ⟨p.val.coeff.support,
        fun a ↦ ⟨p.val.coeff a, (mem_coefficientIdeal R G I p.val).mp p.property a⟩,
        fun a ↦ by simp⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    ext a
    rfl

/-- The genuine coordinate kernel has precisely the ideal-valued character coordinates. -/
def idealCoefficientsEquiv : (G →₀ I) ≃ₗ[R] coefficientIdeal R G I :=
  LinearEquiv.ofBijective (fromIdealCoefficients R G I)
    (fromIdealCoefficients_bijective R G I)

/-- The equivalence is the actual coefficient insertion, not a dimension comparison. -/
theorem idealCoefficientsEquiv_coeff (q : G →₀ I) (a : G) :
    (idealCoefficientsEquiv R G I q).val.coeff a = (q a).val := rfl

end FLT.Mazur.DiagonalizableCobar
