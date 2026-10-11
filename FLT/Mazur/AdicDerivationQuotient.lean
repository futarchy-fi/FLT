/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDerivationFiltration
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Relative derivatives on finite adic neighborhoods

The one-step filtration estimate gives actual quotient maps for a relative
derivation. These maps retain the original representatives and commute
with all transitions of the adic neighborhoods.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicDerivationFiltration

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]
  (d : Derivation R A M) (I : Ideal A)

/-- The derivative of an original finite neighborhood, losing only one power of precision. -/
def quotientMap (n : ℕ) : (A ⧸ I ^ (n + 1)) → M ⧸ (I ^ n • (⊤ : Submodule A M)) :=
  Quotient.lift (fun a ↦ Submodule.Quotient.mk (d a))
    (fun _ _ h ↦ quotient_eq d I n (Quotient.sound h))

/-- Every original section maps to its original derivative modulo the target power. -/
@[simp] theorem quotientMap_mk (n : ℕ) (a : A) :
    quotientMap d I n (Ideal.Quotient.mk _ a) = Submodule.Quotient.mk (d a) := rfl

/-- Finite derivatives commute with every ideal-power transition. -/
theorem quotientMap_transition {m n : ℕ} (hmn : m ≤ n) (a : A ⧸ I ^ (n + 1)) :
    Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn))
        (quotientMap d I n a) =
      quotientMap d I m
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- The finite derivative is additive. -/
theorem quotientMap_add (n : ℕ) (a b : A ⧸ I ^ (n + 1)) :
    quotientMap d I n (a + b) = quotientMap d I n a + quotientMap d I n b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg Submodule.Quotient.mk (d.map_add a b)

/-- The finite derivative retains the original relative scalars. -/
theorem quotientMap_smul [IsScalarTower R A M] (n : ℕ) (r : R)
    (a : A ⧸ I ^ (n + 1)) :
    quotientMap d I n (r • a) = r • quotientMap d I n a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact congrArg Submodule.Quotient.mk (d.map_smul r a)

/-- The Leibniz rule on finite neighborhoods uses their original quotient actions. -/
theorem quotientMap_mul (n : ℕ) (a b : A ⧸ I ^ (n + 1)) :
    quotientMap d I n (a * b) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) a • quotientMap d I n b +
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) b • quotientMap d I n a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg Submodule.Quotient.mk (d.leibniz a b)

end FLT.Mazur.AdicDerivationFiltration
