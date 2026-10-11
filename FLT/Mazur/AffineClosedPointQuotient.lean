/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Actual affine point neighborhoods and stalk quotients

At a closed point, the affine ideal-power quotients identify with the
maximal-ideal quotients of the actual scheme stalk. The comparison is induced
by the original germ map and commutes with all ideal-power transitions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineClosedPointQuotient

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme} (U : X.affineOpens) (x : U.1) (hx : IsClosed {(x : X)})

/-- The actual affine point neighborhood is the corresponding quotient of the actual stalk. -/
def equivalence (r : ℕ) :
    (Γ(X, U) ⧸ (U.2.primeIdealOf x).asIdeal ^ r) ≃+*
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r) := by
  let _ := U.2.primeIdealOf_isMaximal_of_isClosed x hx
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let _ := U.2.isLocalization_stalk x
  exact (IsLocalization.AtPrime.equivQuotMaximalIdealPow
    (U.2.primeIdealOf x).asIdeal (X.presheaf.stalk x) r).toRingEquiv

/-- Every affine section maps to its original germ, without a choice of a stalk isomorphism. -/
@[simp] theorem equivalence_mk (r : ℕ) (a : Γ(X, U)) :
    equivalence U x hx r (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (X.presheaf.germ U x x.2 a) := by
  let _ := U.2.primeIdealOf_isMaximal_of_isClosed x hx
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let _ := U.2.isLocalization_stalk x
  exact IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk
    (U.2.primeIdealOf x).asIdeal (X.presheaf.stalk x) r a

/-- Stalk comparison retains every affine ideal-power transition. -/
theorem equivalence_transition {a b : ℕ} (hab : a ≤ b)
    (s : Γ(X, U) ⧸ (U.2.primeIdealOf x).asIdeal ^ b) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (equivalence U x hx b s) =
      equivalence U x hx a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) s) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [equivalence_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, equivalence_mk]

end FLT.Mazur.AffineClosedPointQuotient
