/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# A simple quadratic root identifies its entire principal branch

For a root r of v²+av=b, invert the complementary factor v+r+a. The
localized algebra is the original base ring, with explicit inverse maps.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.QuadraticRootBranchLocalization
open Polynomial
variable {R : Type*} [CommRing R] (a b r : R)

/-- The original monic quadratic, with the constant side separated. -/
def polynomial : R[X] := X ^ 2 + C a * X - C b

/-- The complementary factor that selects the branch through r. -/
def denominator : AdjoinRoot (polynomial a b) :=
  AdjoinRoot.root (polynomial a b) + algebraMap R _ (r + a)

/-- The actual principal-open ring of the quadratic branch. -/
abbrev Branch := Localization.Away (denominator a b r)

variable (hr : r ^ 2 + a * r = b) (hu : IsUnit (r + r + a))

/-- Evaluation at the specified simple root. -/
def evaluation : AdjoinRoot (polynomial a b) →ₐ[R] R :=
  AdjoinRoot.liftAlgHom (polynomial a b) (AlgHom.id R R) r (by
    simpa only [polynomial, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul,
      eval₂_C, AlgHom.coe_toRingHom, AlgHom.id_apply, sub_eq_zero] using hr)

/-- Evaluation retains the specified root. -/
@[simp] theorem evaluation_root :
    evaluation a b r hr (AdjoinRoot.root (polynomial a b)) = r :=
  AdjoinRoot.liftAlgHom_root ..

/-- The complementary factor evaluates to the invertible root separation. -/
theorem evaluation_denominator : evaluation a b r hr (denominator a b r) = r + r + a := by
  simp only [denominator, map_add, evaluation_root, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, add_assoc]

/-- Root evaluation extends over the whole selected principal branch. -/
def branchEvaluation : Branch a b r →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (denominator a b r) (f := evaluation a b r hr)
    (by rw [evaluation_denominator]; exact hu)

/-- Branch evaluation agrees with root evaluation on the original algebra. -/
theorem branchEvaluation_base (z : AdjoinRoot (polynomial a b)) :
    branchEvaluation a b r hr hu (algebraMap _ (Branch a b r) z) = evaluation a b r hr z := by
  rw [branchEvaluation, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

include hr in
/-- Inverting the complementary factor forces the universal root to equal r. -/
theorem branch_root :
    algebraMap (AdjoinRoot (polynomial a b)) (Branch a b r)
      (AdjoinRoot.root (polynomial a b)) = algebraMap R (Branch a b r) r := by
  let A := AdjoinRoot (polynomial a b)
  let v : A := AdjoinRoot.root (polynomial a b)
  have he : v ^ 2 + algebraMap R A a * v = algebraMap R A b := by
    have h := AdjoinRoot.eval₂_root (polynomial a b)
    change (X ^ 2 + C a * X - C b).eval₂ (algebraMap R A) v = 0 at h
    simpa only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul,
      eval₂_C, sub_eq_zero] using h
  have hr' : (algebraMap R A r) ^ 2 + algebraMap R A a * algebraMap R A r =
      algebraMap R A b := by
    simpa only [map_add, map_pow, map_mul] using congrArg (algebraMap R A) hr
  have hf : (v - algebraMap R A r) * denominator a b r = 0 := by
    change (v - algebraMap R A r) * (v + algebraMap R A (r + a)) = 0
    rw [map_add]
    linear_combination he - hr'
  have hloc := congrArg (algebraMap A (Branch a b r)) hf
  rw [map_mul, map_zero] at hloc
  have hz := (IsLocalization.Away.algebraMap_isUnit (denominator a b r)).mul_left_eq_zero.mp
    hloc
  simpa only [map_sub, sub_eq_zero, ← IsScalarTower.algebraMap_apply] using hz

/-- The whole selected branch is the base ring, with the actual coefficient map as inverse. -/
def branchEquiv : Branch a b r ≃ₐ[R] R := by
  apply AlgEquiv.ofAlgHom (branchEvaluation a b r hr hu) (Algebra.ofId R (Branch a b r))
  · ext
  · apply IsLocalization.algHom_ext (Submonoid.powers (denominator a b r))
    apply AdjoinRoot.algHom_ext
    change algebraMap R (Branch a b r)
      (branchEvaluation a b r hr hu
        (algebraMap _ _ (AdjoinRoot.root (polynomial a b)))) = _
    rw [branchEvaluation_base, evaluation_root]
    exact (branch_root a b r hr).symm

end FLT.Mazur.QuadraticRootBranchLocalization
