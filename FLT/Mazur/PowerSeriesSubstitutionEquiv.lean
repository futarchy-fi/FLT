/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Formal coordinate automorphisms

Mutually inverse substitutions give algebra automorphisms. In particular,
triangular shears and an invertible substitution in the first coordinate
provide elementary changes of formal plane coordinates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PowerSeriesSubstitutionEquiv
open MvPowerSeries
variable {K σ : Type*} [CommRing K]

/-- Mutually inverse formal coordinate systems induce an algebra isomorphism. -/
def equivalence (a b : σ → MvPowerSeries σ K) (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, subst b (a i) = X i) (hba : ∀ i, subst a (b i) = X i) :
    MvPowerSeries σ K ≃ₐ[K] MvPowerSeries σ K :=
  { substAlgHom ha with
    invFun := subst b
    left_inv := fun f ↦ by
      change subst b (substAlgHom ha f) = f
      rw [substAlgHom_apply, subst_comp_subst_apply ha hb, funext hab, subst_self]
      rfl
    right_inv := fun f ↦ by
      change substAlgHom ha (subst b f) = f
      rw [substAlgHom_apply, subst_comp_subst_apply hb ha, funext hba, subst_self]
      rfl }

@[simp] theorem equivalence_X (a b : σ → MvPowerSeries σ K)
    (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, subst b (a i) = X i) (hba : ∀ i, subst a (b i) = X i) (i : σ) :
    equivalence a b ha hb hab hba (X i) = a i :=
  substAlgHom_X ha i

theorem equivalence_apply (a b : σ → MvPowerSeries σ K)
    (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, subst b (a i) = X i) (hba : ∀ i, subst a (b i) = X i)
    (f : MvPowerSeries σ K) : equivalence a b ha hb hab hba f = subst a f :=
  substAlgHom_apply ha f

theorem subst_univariate (a : σ → MvPowerSeries σ K) (ha : HasSubst a)
    (p : PowerSeries K) (i : σ) :
    subst a (p.subst (X i : MvPowerSeries σ K)) = p.subst (a i) := by
  rw [PowerSeries.subst_def, subst_comp_subst_apply ((PowerSeries.HasSubst.X i).const) ha]
  simp only [subst_X ha]
  rfl

/-- Add a series in the first coordinate to the second coordinate. -/
def shear (h : PowerSeries K) (h0 : h.constantCoeff = 0) :
    MvPowerSeries (Fin 2) K ≃ₐ[K] MvPowerSeries (Fin 2) K := by
  let a : Fin 2 → MvPowerSeries (Fin 2) K := ![X 0, X 1 + h.subst (X 0)]
  let b : Fin 2 → MvPowerSeries (Fin 2) K := ![X 0, X 1 - h.subst (X 0)]
  have hc : constantCoeff (h.subst (X 0 : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) h h0
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (by
    intro i; fin_cases i <;> simp [a, hc])
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (by
    intro i; fin_cases i <;> simp [b, hc])
  apply equivalence a b ha hb
  · intro i
    fin_cases i <;>
      simp [a, subst_add hb, subst_X hb, subst_univariate _ hb, b]
  · intro i
    fin_cases i <;>
      simp [b, subst_sub ha, subst_X ha, subst_univariate _ ha, a]

@[simp] theorem shear_X_zero (h : PowerSeries K) (h0 : h.constantCoeff = 0) :
    shear h h0 (X 0) = X 0 := by
  simp [shear, equivalence_X]
@[simp] theorem shear_X_one (h : PowerSeries K) (h0 : h.constantCoeff = 0) :
    shear h h0 (X 1) = X 1 + h.subst (X 0) := by
  simp [shear, equivalence_X]

/-- An invertible univariate substitution acts on the first coordinate. -/
def firstCoordinate (p : PowerSeries K) (p0 : p.constantCoeff = 0)
    (p1 : IsUnit (p.coeff 1)) :
    MvPowerSeries (Fin 2) K ≃ₐ[K] MvPowerSeries (Fin 2) K := by
  let q := p.substInvOfIsUnit p1
  let a : Fin 2 → MvPowerSeries (Fin 2) K := ![p.subst (X 0), X 1]
  let b : Fin 2 → MvPowerSeries (Fin 2) K := ![q.subst (X 0), X 1]
  have q0 : q.constantCoeff = 0 := PowerSeries.constantCoeff_substInvOfIsUnit p p1
  have hp0 : constantCoeff (p.subst (X 0 : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) p p0
  have hq0 : constantCoeff (q.subst (X 0 : MvPowerSeries (Fin 2) K)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) q q0
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (by
    intro i; fin_cases i <;> simp [a, hp0])
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (by
    intro i; fin_cases i <;> simp [b, hq0])
  apply equivalence a b ha hb
  · intro i
    fin_cases i
    · change subst b (p.subst (X 0)) = X 0
      rw [subst_univariate _ hb]
      change p.subst (q.subst (X 0 : MvPowerSeries (Fin 2) K)) = X 0
      rw [← PowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' q0) (PowerSeries.HasSubst.X 0)]
      rw [PowerSeries.subst_substInvOfIsUnit_right p p0 p1]
      exact PowerSeries.subst_X (PowerSeries.HasSubst.X 0)
    · simp [a, subst_X hb, b]
  · intro i
    fin_cases i
    · change subst a (q.subst (X 0)) = X 0
      rw [subst_univariate _ ha]
      change q.subst (p.subst (X 0 : MvPowerSeries (Fin 2) K)) = X 0
      rw [← PowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' p0) (PowerSeries.HasSubst.X 0)]
      rw [PowerSeries.subst_substInvOfIsUnit_left p p0 p1]
      exact PowerSeries.subst_X (PowerSeries.HasSubst.X 0)
    · simp [b, subst_X ha, a]

@[simp] theorem firstCoordinate_X_zero (p : PowerSeries K) (p0 : p.constantCoeff = 0)
    (p1 : IsUnit (p.coeff 1)) :
    firstCoordinate p p0 p1 (X 0) = p.subst (X 0) := by
  simp [firstCoordinate, equivalence_X]
@[simp] theorem firstCoordinate_X_one (p : PowerSeries K) (p0 : p.constantCoeff = 0)
    (p1 : IsUnit (p.coeff 1)) :
    firstCoordinate p p0 p1 (X 1) = X 1 := by
  simp [firstCoordinate, equivalence_X]

theorem firstCoordinate_univariate (p : PowerSeries K) (p0 : p.constantCoeff = 0)
    (p1 : IsUnit (p.coeff 1)) (h : PowerSeries K) :
    firstCoordinate p p0 p1 (h.subst (X 0)) =
      h.subst (p.subst (X 0 : MvPowerSeries (Fin 2) K)) := by
  simp only [firstCoordinate, equivalence_apply]
  apply subst_univariate
  apply hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i
  · exact PowerSeries.constantCoeff_subst_eq_zero (by simp) p p0
  · simp

/-- Subtract the second coordinate from the first. -/
def subtractSecond : MvPowerSeries (Fin 2) K ≃ₐ[K] MvPowerSeries (Fin 2) K := by
  let a : Fin 2 → MvPowerSeries (Fin 2) K := ![X 0 - X 1, X 1]
  let b : Fin 2 → MvPowerSeries (Fin 2) K := ![X 0 + X 1, X 1]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (by
    intro i; fin_cases i <;> simp [a])
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (by
    intro i; fin_cases i <;> simp [b])
  apply equivalence a b ha hb
  · intro i
    fin_cases i <;> simp [a, subst_sub hb, subst_X hb, b]
  · intro i
    fin_cases i <;> simp [b, subst_add ha, subst_X ha, a]

@[simp] theorem subtractSecond_X_zero :
    subtractSecond (K := K) (X 0) = X 0 - X 1 := by
  simp [subtractSecond, equivalence_X]
@[simp] theorem subtractSecond_X_one :
    subtractSecond (K := K) (X 1) = X 1 := by
  simp [subtractSecond, equivalence_X]
end FLT.Mazur.PowerSeriesSubstitutionEquiv
