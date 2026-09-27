/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointReductionKernel
public import Mathlib.Data.Set.Finite.Basic

/-!
# The specialization homomorphism

Coordinate reduction is additive over an algebraically closed valued field with
elliptic generic and special fibers. The proof combines addition on the integral
chart with translation by points reducing to infinity. An auxiliary point avoids
opposite reductions, so no separate exceptional-denominator calculation is needed.
The resulting homomorphism is surjective on positive integer torsion.
-/

@[expose] public section

/-- A surjective map to an infinite group is additive if it preserves every sum
whose proposed image is nonzero. -/
private theorem map_add_of_add_ne_zero {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Infinite H] (f : G → H) (hsurj : Function.Surjective f)
    (hadd : ∀ x y, f x + f y ≠ 0 → f (x + y) = f x + f y) :
    ∀ x y, f (x + y) = f x + f y := by
  classical
  intro x y
  obtain ⟨t, ht⟩ := Finset.exists_notMem ({-f y, -(f x + f y), -f (x + y)} : Finset H)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  obtain ⟨z, rfl⟩ := hsurj t
  have h₁ : f y + f z ≠ 0 := fun he => ht.1 (eq_neg_of_add_eq_zero_right he)
  have h₂ : f x + (f y + f z) ≠ 0 := by
    intro he
    exact ht.2.1 (eq_neg_of_add_eq_zero_right (by simpa only [add_assoc] using he))
  have h₃ : f (x + y) + f z ≠ 0 := fun he => ht.2.2 (eq_neg_of_add_eq_zero_right he)
  have he : f (x + y) + f z = (f x + f y) + f z := by
    rw [← hadd (x + y) z h₃, add_assoc, hadd x (y + z) (by rwa [hadd y z h₁]),
      hadd y z h₁, add_assoc]
  exact add_right_cancel he

open Polynomial IsLocalRing
namespace WeierstrassCurve
variable {K : Type*} [Field K] [IsAlgClosed K] (E : WeierstrassCurve K)
/-- Every x-coordinate on a Weierstrass equation over an algebraically closed field
has a corresponding y-coordinate. -/
theorem exists_equation_y (x : K) : ∃ y : K, E.toAffine.Equation x y := by
  let f := E.toAffine.polynomial.map (evalRingHom x)
  have hmonic : f.Monic := Affine.monic_polynomial.map _
  have hdeg : f.natDegree = 2 := by
    exact (Affine.monic_polynomial.natDegree_map _).trans Affine.natDegree_polynomial
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root f (by
    rw [degree_eq_natDegree hmonic.ne_zero, hdeg]
    decide)
  exact ⟨y, by simpa [f, IsRoot, eval_map, eval₂_evalRingHom, Affine.Equation] using hy⟩
/-- An elliptic curve over an algebraically closed field has infinitely many points. -/
theorem infinite_point [E.IsElliptic] : Infinite E.toAffine.Point := by
  classical
  let f (x : K) : E.toAffine.Point :=
    .some x (E.exists_equation_y x).choose
      (Affine.equation_iff_nonsingular.mp (E.exists_equation_y x).choose_spec)
  apply Infinite.of_injective f
  intro x y h
  exact (Affine.Point.some.inj h).1

variable (A : ValuationSubring K) (W : WeierstrassCurve A)
  [(W.map (algebraMap A K)).IsElliptic] [(W.map (residue A)).IsElliptic]

/-- Every geometric special-fiber point lifts to a generic-fiber point. -/
theorem reducePoint_surjective : Function.Surjective (W.reducePoint A) := by
  intro P
  cases P with
  | zero => exact ⟨0, rfl⟩
  | some x y h =>
    obtain ⟨a, rfl⟩ := residue_surjective x
    obtain ⟨b, hab, rfl⟩ := W.exists_equation_lifting A a y h.1
    have hab' : (W.map (algebraMap A K)).toAffine.Nonsingular
        (algebraMap A K a) (algebraMap A K b) :=
      Affine.equation_iff_nonsingular.mp (hab.map (algebraMap A K))
    refine ⟨.some _ _ hab', ?_⟩
    exact W.reducePoint_some A a b hab'

/-- Translation by points reducing to infinity suffices for full additivity. -/
private theorem reducePoint_add_of_kernel_translation [DecidableEq K] [DecidableEq (ResidueField A)]
    (hker : ∀ P Q, W.reducePoint A P = 0 → W.reducePoint A Q ≠ 0 →
      W.reducePoint A (P + Q) = W.reducePoint A Q)
    (P Q : (W.map (algebraMap A K)).toAffine.Point) :
    W.reducePoint A (P + Q) = W.reducePoint A P + W.reducePoint A Q := by
  have : Infinite (W.map (residue A)).toAffine.Point :=
    (W.map (residue A)).infinite_point
  apply map_add_of_add_ne_zero (W.reducePoint A) (W.reducePoint_surjective A) ?_ P Q
  intro P Q hsum
  by_cases hp : W.reducePoint A P = 0
  · rw [hp, zero_add] at hsum ⊢
    exact hker P Q hp hsum
  by_cases hq : W.reducePoint A Q = 0
  · rw [hq, add_zero] at hsum ⊢
    rw [add_comm]
    exact hker Q P hq hsum
  cases P with
  | zero => exact (hp rfl).elim
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact (hq rfl).elim
    | some x₂ y₂ h₂ =>
      have hi₁ : x₁ ∈ A ∧ y₁ ∈ A := by
        by_contra hn
        exact hp (by simp only [reducePoint, dite_eq_right hn]; rfl)
      have hi₂ : x₂ ∈ A ∧ y₂ ∈ A := by
        by_contra hn
        exact hq (by simp only [reducePoint, dite_eq_right hn]; rfl)
      apply W.reducePoint_add_of_residue_ne_neg A ⟨x₁, hi₁.1⟩ ⟨y₁, hi₁.2⟩
        ⟨x₂, hi₂.1⟩ ⟨y₂, hi₂.2⟩ h₁ h₂
      intro he
      change W.reducePoint A (.some x₁ y₁ h₁) = -W.reducePoint A (.some x₂ y₂ h₂) at he
      exact hsum (by rw [he, neg_add_cancel])

/-- Coordinate reduction commutes with addition. -/
theorem reducePoint_add [DecidableEq K] [DecidableEq (ResidueField A)]
    (P Q : (W.map (algebraMap A K)).toAffine.Point) :
    W.reducePoint A (P + Q) = W.reducePoint A P + W.reducePoint A Q := by
  apply W.reducePoint_add_of_kernel_translation A ?_ P Q
  intro P Q hp hq
  cases P with
  | zero => exact congrArg (W.reducePoint A) (zero_add Q)
  | some x y h =>
    cases Q with
    | zero => exact (hq rfl).elim
    | some u v h' =>
      have hx : x ∉ A := by
        intro hx
        have hy := W.mem_y_of_mem_x A h.1 hx
        have he := W.reducePoint_some A ⟨x, hx⟩ ⟨y, hy⟩ h
        have hh : Affine.Point.some (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)
            (W.nonsingular_residue_of_nonsingular A h) = 0 := he.symm.trans hp
        exact Affine.Point.some_ne_zero _ hh
      have hi : u ∈ A ∧ v ∈ A := by
        by_contra hn
        exact hq (by simp only [reducePoint, dite_eq_right hn]; rfl)
      exact W.reducePoint_add_nonintegral_integral A ⟨u, hi.1⟩ ⟨v, hi.2⟩ h h' hx

/-- The specialization homomorphism on geometric points. -/
noncomputable def reducePointAddHom [DecidableEq K] [DecidableEq (ResidueField A)] :
    (W.map (algebraMap A K)).toAffine.Point →+ (W.map (residue A)).toAffine.Point where
  toFun := W.reducePoint A
  map_zero' := rfl
  map_add' := W.reducePoint_add A

/-- The specialization homomorphism restricted to integer torsion. -/
noncomputable def reduceTorsionAddHom [DecidableEq K] [DecidableEq (ResidueField A)] (n : ℕ) :
    Submodule.torsionBy ℤ (W.map (algebraMap A K)).toAffine.Point (n : ℤ) →+
      Submodule.torsionBy ℤ (W.map (residue A)).toAffine.Point (n : ℤ) where
  toFun := W.reduceTorsion A n
  map_zero' := rfl
  map_add' P Q := Subtype.ext (W.reducePoint_add A P.val Q.val)

/-- Specialization is surjective on every positive integer torsion subgroup. -/
theorem reduceTorsionAddHom_surjective [DecidableEq K] [DecidableEq (ResidueField A)]
    {n : ℕ} (hn : 0 < n) : Function.Surjective (W.reduceTorsionAddHom A n) :=
  W.reduceTorsion_surjective A hn
end WeierstrassCurve
