/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Perfect

/-!
# Mixed-characteristic coefficients with a specified finite residue field

The coefficient ring is the actual Witt ring. Its residue identification and
p-adic scalar embedding are constructed, rather than supplied as hypotheses.
This does not assert nonvanishing of an arithmetic deformation quotient.
-/

@[expose] public noncomputable section
namespace Deformation.WittCoefficients
variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- The prime-field Witt vectors give the integral p-adic scalar map. -/
def padicMap : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
    (WittVector.equiv p).symm.toRingHom

/-- The scalar map is an embedding. -/
theorem padicMap_injective : Function.Injective (padicMap p k) :=
  (WittVector.map_injective _ (ZMod.castHom (dvd_refl p) k).injective).comp
    (WittVector.equiv p).symm.injective

/-- Use this scope when installing the constructed coefficient algebra. -/
scoped instance padicAlgebra : Algebra ℤ_[p] (WittVector p k) := (padicMap p k).toAlgebra

/-- Characteristic zero follows from the actual p-adic embedding. -/
scoped instance charZero : CharZero (WittVector p k) :=
  charZero_of_injective_ringHom (padicMap_injective p k)

variable [Finite k]

/-- The coefficient ring has uniformizer p, not merely residue characteristic p. -/
theorem maximalIdeal_eq : IsLocalRing.maximalIdeal (WittVector p k) =
    Ideal.span {(p : WittVector p k)} :=
  (WittVector.irreducible p).maximalIdeal_eq

/-- Its actual local residue field is the specified field. -/
def residueEquiv : IsLocalRing.ResidueField (WittVector p k) ≃+* k :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq p k)).trans WittVector.quotientPEquiv

/-- Residue identification sends a Witt vector to its constant coefficient. -/
theorem residueEquiv_residue (x : WittVector p k) :
    residueEquiv p k (IsLocalRing.residue _ x) = WittVector.constantCoeff x := rfl

/-- The finite residue-field hypothesis required by the deformation category. -/
scoped instance finiteResidue : Finite (IsLocalRing.ResidueField (WittVector p k)) :=
  Finite.of_injective (residueEquiv p k) (residueEquiv p k).injective

/-- Completeness is for the maximal ideal of this same coefficient ring. -/
scoped instance adicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (WittVector p k)) (WittVector p k) := by
  rw [maximalIdeal_eq]
  infer_instance

omit [Finite k] in
/-- Every power of p survives in the coefficient base. This says nothing yet about a quotient. -/
theorem p_pow_ne_zero (n : ℕ) : (p : WittVector p k) ^ n ≠ 0 :=
  pow_ne_zero n (WittVector.p_nonzero p k)

end Deformation.WittCoefficients
