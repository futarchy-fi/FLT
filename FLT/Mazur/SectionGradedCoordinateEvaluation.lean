/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedAlgebra
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Evaluation of section rings in line coordinates

A line trivialization evaluates every tensor degree in the structure sheaf.
When a homogeneous denominator has unit coordinate, evaluation extends to
the degree-zero localization that defines the corresponding Proj chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum
universe u
namespace FLT.Mazur.SectionGradedCoordinateEvaluation
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum
open SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {L : X.Modules} (e : L ≅ structureModule X) (U : X.Opens)

/-- Sum the coordinates of all homogeneous components in a chosen trivialization. -/
def sumEval : SectionGradedSum.Sections L U →+ Γ(X, U) :=
  DirectSum.toAddMonoid (fun n ↦ ((tensorPowerTrivialization e n).hom.app U).hom)

/-- Evaluation on a homogeneous summand is its actual tensor-power coordinate. -/
lemma sumEval_of (n : ℕ) (s : Piece L U n) :
    sumEval e U (of L U n s) = coordinate e n U s :=
  DirectSum.toAddMonoid_of _ n s

/-- Summing coordinates is multiplicative on arbitrary finite sums. -/
lemma sumEval_mul (a b : SectionGradedSum.Sections L U) :
    sumEval e U (a * b) = sumEval e U a * sumEval e U b := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m s =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of n t =>
      change sumEval e U (of L U m s * of L U n t) =
        sumEval e U (of L U m s) * sumEval e U (of L U n t)
      rw [mul_of, sumEval_of, sumEval_of, sumEval_of, coordinate_mul]
    | add b c hb hc => simp only [_root_.mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [_root_.add_mul, map_add, ha, hc]

/-- The coordinate evaluation is a unital homomorphism of the full section ring. -/
def ringEval : SectionGradedSum.Sections L U →+* Γ(X, U) where
  __ := sumEval e U
  map_one' := by
    change sumEval e U (of L U 0 (1 : Γ(X, U))) = 1
    rw [sumEval_of]
    rfl
  map_mul' := sumEval_mul e U

/-- Coordinate evaluation retains the homogeneous coordinate formula. -/
lemma ringEval_of (n : ℕ) (s : Piece L U n) :
    ringEval e U (of L U n s) = coordinate e n U s := sumEval_of e U n s

variable [Fact (LocallyFreeRankOne L)]

/-- Evaluate the homogeneous localization on a chart where the denominator is a unit. -/
def awayEval (f : SectionGradedSum.Sections L U) (hf : IsUnit (ringEval e U f)) :
    HomogeneousLocalization.Away (grade L U) f →+* Γ(X, U) :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hf).comp
    (algebraMap (HomogeneousLocalization.Away (grade L U) f) (Localization.Away f))

/-- Multiplication by the denominator recovers the numerator after chart evaluation. -/
lemma awayEval_mk_mul (f : SectionGradedSum.Sections L U) (hf : IsUnit (ringEval e U f))
    (c : HomogeneousLocalization.NumDenSameDeg (grade L U) (Submonoid.powers f)) :
    awayEval e U f hf (HomogeneousLocalization.mk c) * ringEval e U c.den =
      ringEval e U c.num := by
  let φ := IsLocalization.Away.lift (S := Localization.Away f) f hf
  change φ (HomogeneousLocalization.mk c).val * ringEval e U c.den = _
  rw [← IsLocalization.Away.lift_eq (S := Localization.Away f) f hf c.den,
    ← IsLocalization.Away.lift_eq (S := Localization.Away f) f hf c.num, ← map_mul]
  congr 1
  simpa only [HomogeneousLocalization.val_mk, Localization.mk_eq_mk'] using
    IsLocalization.mk'_spec (Localization.Away f)
      (c.num : SectionGradedSum.Sections L U) ⟨c.den, c.den_mem⟩

end FLT.Mazur.SectionGradedCoordinateEvaluation
