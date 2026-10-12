/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData
public import FLT.Mazur.NodeTangentShear

/-!
# Coefficient extension and shearing of actual divided data

Transport the original coefficient factorizations, including the fourth
coefficient's correction. The distinguished tangent root gives a concrete
family of divided data for the split integral equation at every depth.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassCurve
variable {R S : Type*} [CommRing R] [CommRing S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}

/-- Extend the actual coefficient quotients along any ring map. -/
def coefficientData (d : Data W π k) (f : R →+* S) : Data (W.map f) (f π) k where
  b3 := f d.b3
  b4 := f d.b4
  b6 := f d.b6
  factor3 := by simpa only [map_a₃, map_mul, map_pow] using congrArg f d.factor3
  factor4 := by simpa only [map_a₄, map_mul, map_pow] using congrArg f d.factor4
  factor6 := by simpa only [map_a₆, map_mul, map_pow] using congrArg f d.factor6

/-- The unit shear used on every original divided chart. -/
def rootShearCurve (W : WeierstrassCurve R) (r : R) : WeierstrassCurve R :=
  (⟨1, 0, r, 0⟩ : VariableChange R) • W

/-- All five coefficients of the shear, before imposing a tangent-root equation. -/
theorem rootShearCurve_coefficients (r : R) :
    (rootShearCurve W r).a₁ = W.a₁ + 2 * r ∧
      (rootShearCurve W r).a₂ = W.a₂ - r * W.a₁ - r ^ 2 ∧
      (rootShearCurve W r).a₃ = W.a₃ ∧
      (rootShearCurve W r).a₄ = W.a₄ - r * W.a₃ ∧
      (rootShearCurve W r).a₆ = W.a₆ := by
  simp only [rootShearCurve, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul,
    zero_mul, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0)]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The shear changes b4 by r*b3 and preserves both other depth quotients. -/
def shearData (d : Data W π k) (r : R) : Data (rootShearCurve W r) π k where
  b3 := d.b3
  b4 := d.b4 - r * d.b3
  b6 := d.b6
  factor3 := (rootShearCurve_coefficients r).2.2.1.trans d.factor3
  factor4 := by
    rw [(rootShearCurve_coefficients r).2.2.2.1, d.factor4, d.factor3]
    ring
  factor6 := (rootShearCurve_coefficients r).2.2.2.2.trans d.factor6

/-- The actual tangent extension and shear carry the original data at every depth. -/
def tangentShearData (d : Data W π k) :
    Data (nodeTangentShear W) (algebraMap R _ π) k :=
  shearData (coefficientData d (algebraMap R _))
    (AdjoinRoot.root (nodeTangentPolynomial W))

/-- The tangent divided equation retains its original third quotient. -/
theorem tangentShearData_b3 (d : Data W π k) :
    (tangentShearData d).b3 = algebraMap R _ d.b3 := rfl

/-- The fourth quotient retains the correction by the distinguished tangent root. -/
theorem tangentShearData_b4 (d : Data W π k) :
    (tangentShearData d).b4 = algebraMap R _ d.b4 -
      AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap R _ d.b3 := rfl

/-- The constant quotient is unchanged by the shear. -/
theorem tangentShearData_b6 (d : Data W π k) :
    (tangentShearData d).b6 = algebraMap R _ d.b6 := rfl

end FLT.Mazur.WeierstrassDividedDepth
