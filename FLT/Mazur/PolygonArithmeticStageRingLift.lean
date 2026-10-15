/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PowerSeriesArithmeticCompletion

/-!
# Reconstructing ring maps over the original complete arithmetic base

Adjacent-compatible maps to the actual arithmetic quotients reconstruct a
ring map to the original complete ring. Every original quotient map is
retained, and these maps jointly detect equality.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonArithmeticStages

variable (A : Type*) [CommRing A] (π : A)
  {B : Type*} [CommRing B] (f : ∀ m, B →+* Quotient A π m)
  (hf : ∀ m, (restriction A π m).toRingHom.comp (f (m + 1)) = f m)

include hf in
/-- Adjacent compatibility implies compatibility for every original quotient factor. -/
theorem arithmeticStageRing_compatible {a b : ℕ} (hab : a ≤ b) (x : B) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))
      (f b x) = f a x := by
  induction b, hab using Nat.le_induction with
  | base => simp only [Ideal.Quotient.factor_eq, RingHom.id_apply]
  | succ b hab ih =>
    have he := DFunLike.congr_fun (hf b) x
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (b + 1)))
      (f (b + 1) x) = f b x at he
    rw [← he] at ih
    simpa only [Ideal.Quotient.factor_comp_apply] using ih

/-- The original finite coefficient maps as actual compatible quotient sections. -/
def arithmeticStageRingSections : B →+* AdicCompletionPositiveLimit.sections (ideal A π) where
  toFun x := ⟨fun m ↦ f m x, fun hab ↦ arithmeticStageRing_compatible A π f hf hab x⟩
  map_one' := Subtype.ext (funext fun m ↦ map_one (f m))
  map_mul' x y := Subtype.ext (funext fun m ↦ map_mul (f m) x y)
  map_zero' := Subtype.ext (funext fun m ↦ map_zero (f m))
  map_add' x y := Subtype.ext (funext fun m ↦ map_add (f m) x y)

variable [IsAdicComplete (ideal A π) A]

/-- Reconstruct the actual ring map into the original complete arithmetic coefficients. -/
def arithmeticStageRingLift : B →+* A :=
  (AdicCompletion.ofAlgEquiv (ideal A π)).symm.toRingHom.comp
    ((AdicCompletionPositiveLimit.fromSections (ideal A π)).comp
      (arithmeticStageRingSections A π f hf))

/-- The reconstructed map has exactly the prescribed quotient at every order. -/
theorem quotient_arithmeticStageRingLift (m : ℕ) (x : B) :
    Ideal.Quotient.mk (ideal A π ^ (m + 1)) (arithmeticStageRingLift A π f hf x) =
      f m x := by
  change Ideal.Quotient.mk _ ((AdicCompletion.ofAlgEquiv _).symm _) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm]
  exact AdicCompletionPositiveLimit.eval_fromSections _ _ _

/-- Actual positive-order arithmetic quotients jointly detect original coefficients. -/
theorem arithmeticQuotient_ext {x y : A}
    (he : ∀ m, Ideal.Quotient.mk (ideal A π ^ (m + 1)) x =
      Ideal.Quotient.mk (ideal A π ^ (m + 1)) y) : x = y := by
  apply (AdicCompletion.ofAlgEquiv (ideal A π)).injective
  apply (AdicCompletionPositiveLimit.equivalence (ideal A π)).injective
  apply Subtype.ext
  funext m
  exact he m

/-- The reconstructed ring map is uniquely specified by its original arithmetic quotients. -/
theorem arithmeticStageRingLift_unique (g : B →+* A)
    (hg : ∀ m, (Ideal.Quotient.mk (ideal A π ^ (m + 1))).comp g = f m) :
    g = arithmeticStageRingLift A π f hf := by
  ext x : 1
  apply arithmeticQuotient_ext A π
  intro m
  rw [quotient_arithmeticStageRingLift]
  exact DFunLike.congr_fun (hg m) x

end FLT.Mazur.PolygonArithmeticStages
