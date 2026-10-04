/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Reduction kernels for integral coefficient thickenings -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PadicHodgeTheory
variable {A B : Type*} [CommRing A] [CommRing B]

/-- Pulling a coefficient ideal back through a surjection adds precisely its kernel. -/
theorem integralReduction_ker (f : A →+* B) (hf : Function.Surjective f) (J : Ideal A) :
    RingHom.ker ((Ideal.Quotient.mk (J.map f)).comp f) = J ⊔ RingHom.ker f := by
  rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective f hf]
  rfl

/-- Quotienting by a smaller ideal retains the exact original reduction kernel. -/
theorem integralFactor_ker {I J : Ideal A} (h : I ≤ J) :
    RingHom.ker (Ideal.Quotient.factor h) = J.map (Ideal.Quotient.mk I) := by
  rw [Ideal.Quotient.factor, Ideal.ker_quotient_lift, Ideal.mk_ker]

/-- A power containment upstairs proves nilpotence downstairs. -/
theorem integralFactor_ker_pow {I J : Ideal A} (h : I ≤ J) (n : ℕ)
    (hn : J ^ n ≤ I) : RingHom.ker (Ideal.Quotient.factor h) ^ n = ⊥ := by
  rw [integralFactor_ker, ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le hn

end PadicHodgeTheory
