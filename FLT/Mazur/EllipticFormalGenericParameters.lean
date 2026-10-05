/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalSubstitution

/-!
# Distinct generic formal parameters

Restricting to a coordinate axis proves that a formal sum of two other variables
cannot equal that variable. This lets the secant comparison prove associativity
on three independent variables without a separate tangent computation.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open MvPowerSeries

variable {R : Type*} [CommRing R] [Nontrivial R] {σ : Type*} [Finite σ]

/-- A sum of two variables is different from an independent third variable. -/
theorem add_X_X_ne_X (W : WeierstrassCurve R) {i j k : σ} (hik : i ≠ k) (hjk : j ≠ k) :
    add W (X i) (X j) ≠ (X k : MvPowerSeries σ R) := by
  classical
  let a : σ → PowerSeries R := fun r => if r = k then PowerSeries.X else 0
  have ha0 : ∀ r, MvPowerSeries.constantCoeff (a r) = 0 := by
    intro r
    simp only [a]
    split_ifs <;> simp [PowerSeries.X]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  intro h
  have he := congrArg (substAlgHom ha) h
  rw [substitution_add W ha ha0 (by simp) (by simp)] at he
  simp only [coe_substAlgHom, subst_X ha, a, ite_eq_right hik, ite_eq_right hjk,
    ite_eq_left rfl] at he
  rw [add_zero W (by simp)] at he
  exact PowerSeries.X_ne_zero he.symm

end FLT.Mazur.FormalInfinity
