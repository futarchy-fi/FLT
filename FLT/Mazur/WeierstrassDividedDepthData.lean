/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationHorizontalCongruence
public import FLT.Mazur.WeierstrassSuccessiveXDepthComparison

/-!
# Actual coefficient data for finite divided depths

A datum records only factorizations of the original Weierstrass coefficients.
Its scheme, horizontal open and contraction are constructed from the equation.
No modification, smoothness, properness or classification is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π : R)

/-- Quotients of the same original coefficients at a specified depth. -/
structure Data (k : ℕ) where
  /-- The depth quotient for the original coefficient b3. -/
  b3 : R
  /-- The depth quotient for the original coefficient b4. -/
  b4 : R
  /-- The depth quotient for the original coefficient b6. -/
  b6 : R
  factor3 : W.a₃ = π ^ k * b3
  factor4 : W.a₄ = π ^ k * b4
  factor6 : W.a₆ = (π ^ k) ^ 2 * b6

variable {W π} {k : ℕ}

/-- The actual divided equation scheme at the specified depth. -/
def chart (d : Data W π k) : Scheme :=
  Spec (.of (WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6))

/-- Its actual horizontal principal open. -/
def boundary (d : Data W π k) : Scheme :=
  Spec (.of (WeierstrassDilatation.HorizontalCoordinate W (π ^ k) d.b3 d.b4 d.b6))

/-- The boundary's canonical inclusion into its divided chart. -/
def boundaryInclusion (d : Data W π k) : boundary d ⟶ chart d :=
  WeierstrassDilatation.horizontalInclusion W (π ^ k) d.b3 d.b4 d.b6

instance boundaryInclusion_isOpenImmersion (d : Data W π k) :
    IsOpenImmersion (boundaryInclusion d) := by
  unfold boundaryInclusion
  infer_instance

/-- The actual map to the original projective Weierstrass cubic. -/
def toCurve (d : Data W π k) : chart d ⟶ WeierstrassIntegralChart.integralCurve W :=
  WeierstrassDilatation.toCurve W (π ^ k) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6

/-- Depth zero is available for every original equation. -/
def zeroData : Data W π 0 where
  b3 := W.a₃
  b4 := W.a₄
  b6 := W.a₆
  factor3 := by simp
  factor4 := by simp
  factor6 := by simp

variable [IsDomain R] (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))

include hπ in
/-- Consecutive third coefficients have the forced uniformizer factor. -/
theorem factor3_step : d.b3 = π * e.b3 := by
  simpa using WeierstrassDilatation.depth_coefficient_factor π k (k + 1) hπ
    (Nat.le_succ k) d.factor3 e.factor3

include hπ in
/-- Consecutive fourth coefficients have the same forced factor. -/
theorem factor4_step : d.b4 = π * e.b4 := by
  simpa using WeierstrassDilatation.depth_coefficient_factor π k (k + 1) hπ
    (Nat.le_succ k) d.factor4 e.factor4

include hπ in
/-- Consecutive constant coefficients have the forced square factor. -/
theorem factor6_step : d.b6 = π ^ 2 * e.b6 := by
  simpa using WeierstrassDilatation.depth_constant_factor π k (k + 1) hπ
    (Nat.le_succ k) d.factor6 e.factor6

/-- The actual transition of consecutive divided depths. -/
def transition : chart e ⟶ chart d :=
  WeierstrassDilatation.depthTransitionMorphism π k (k + 1) hπ (Nat.le_succ k)
    W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6
    e.factor3 e.factor4 e.factor6

/-- Every actual depth transition retains the original cubic map. -/
@[reassoc] theorem transition_toCurve : transition hπ d e ≫ toCurve d = toCurve e :=
  WeierstrassDilatation.depthTransitionMorphism_contraction π k (k + 1) hπ
    (Nat.le_succ k) W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
    d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6

end FLT.Mazur.WeierstrassDividedDepth
