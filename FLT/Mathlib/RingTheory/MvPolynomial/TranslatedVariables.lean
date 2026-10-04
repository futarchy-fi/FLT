/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.VariableRegularSequence
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Translating a regular sequence of polynomial variables -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Translation of the variables by a tuple of scalars. -/
def translateVariables (a : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval fun i ↦ X i - C (a i)) (aeval fun i ↦ X i + C (a i))
    (by ext i; simp) (by ext i; simp)

@[simp]
theorem translateVariables_X (a : σ → R) (i : σ) :
    translateVariables a (X i) = X i - C (a i) := by
  simp [translateVariables]

/-- The differences from a rational point form a regular sequence in any distinct order. -/
theorem isRegular_X_sub_C_list [Nontrivial R] (a : σ → R) {is : List σ}
    (hi : is.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (is.map fun i ↦ X i - C (a i)) := by
  apply ((translateVariables a).toAddEquiv.isRegular_congr (as := is.map (X (R := R)))
    (bs := is.map fun i ↦ X i - C (a i)) ?_).mp (isRegular_X_list hi)
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro i _ f
  simp [smul_eq_mul]

end MvPolynomial
