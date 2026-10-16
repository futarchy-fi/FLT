/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalPolygonBoundary
public import FLT.Mazur.NodalFiberUnitScalingBoundary
public import FLT.Mazur.WeierstrassDilatationFixedTerminalPolygon
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureUnits

/-!
# Both actual terminal boundaries in the fixed normalized smoothing

The full first and second factors use the same target smoothing as the
initial and retained depth-one maps. These factorizations retain every term;
equality with the last retained edge parameters is still a separate obligation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
  (u : Rˣ) (hprimitive : Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) = π * ↑u)
include hprimitive
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W ha (π ^ 1) π m
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "c" => arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "v" => arithmeticFixedTerminalUnit π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive m
local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6
local notation "P" => fixedTerminalPolygonIso π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive m

/-- The corrected full first-factor unit at the original opposite terminal boundary. -/
def fixedTerminalPolygonFirstBoundaryUnit : Q[T;T⁻¹]ˣ :=
  NodalFiber.unitNormalizedFirstUnit c v (E true) (by
    simpa only [↓reduceIte] using
      terminalArithmeticSelected_unit data m j hj ha hs h2 h3 h4 h6 true)

omit hprimitive in
/-- The full original second-factor unit at the small terminal boundary. -/
def fixedTerminalPolygonSecondBoundaryUnit : Q[T;T⁻¹]ˣ :=
  (terminalArithmeticSelected_unit data m j hj ha hs h2 h3 h4 h6 false).unit

/-- The exact change from the original Laurent parameter to the polygon boundary parameter. -/
def fixedTerminalPolygonBoundaryParameter (opposite : Bool) :
    PolygonSmoothing.branchTorus Q ⟶ PolygonSmoothing.branchTorus Q :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
    (if opposite then fixedTerminalPolygonFirstBoundaryUnit data m j hj
      ha hs h2 h3 h4 h6 u hprimitive
    else fixedTerminalPolygonSecondBoundaryUnit data m j hj ha hs h2 h3 h4 h6)).toRingHom)

/-- The opposite terminal boundary retains its full corrected first-factor parameter. -/
@[reassoc] theorem fixedTerminalPolygon_first_boundary :
    Spec.map (CommRingCat.ofHom (E true).toRingHom) ≫ (P).hom =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
        (fixedTerminalPolygonFirstBoundaryUnit data m j hj
          ha hs h2 h3 h4 h6 u hprimitive)).toRingHom) ≫
          PolygonSmoothing.leftBranchOpen Q τ := by
  exact NodalFiber.unitSmoothingIso_first_boundary c τ v
    (arithmeticFixedTerminalUnit_spec π W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
      ha hs₂ h2 h3 h4 h6 u hprimitive m) (E true) _

/-- The small terminal boundary keeps the full original second-factor Laurent parameter. -/
@[reassoc] theorem fixedTerminalPolygon_second_boundary :
    Spec.map (CommRingCat.ofHom (E false).toRingHom) ≫ (P).hom =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
        (fixedTerminalPolygonSecondBoundaryUnit data m j hj ha hs h2 h3 h4 h6)).toRingHom) ≫
          PolygonSmoothing.rightBranchOpen Q τ := by
  exact NodalFiber.unitSmoothingIso_second_boundary c τ v
    (arithmeticFixedTerminalUnit_spec π W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
      ha hs₂ h2 h3 h4 h6 u hprimitive m) (E false) _

/-- Both original boundary labels retain their actual normalized Laurent parameter maps. -/
@[reassoc] theorem fixedTerminalPolygon_boundary (opposite : Bool) :
    Spec.map (CommRingCat.ofHom (E opposite).toRingHom) ≫ (P).hom =
      fixedTerminalPolygonBoundaryParameter data m j hj ha hs h2 h3 h4 h6 u hprimitive opposite ≫
        (if opposite then PolygonSmoothing.leftBranchOpen Q τ
        else PolygonSmoothing.rightBranchOpen Q τ) := by
  cases opposite
  · exact fixedTerminalPolygon_second_boundary data m j hj ha hs h2 h3 h4 h6 u hprimitive
  · exact fixedTerminalPolygon_first_boundary data m j hj ha hs h2 h3 h4 h6 u hprimitive

/-- Changing the target smoothing multiplies the entire first parameter by the initial unit. -/
theorem fixedTerminalPolygonFirstBoundaryUnit_eq :
    fixedTerminalPolygonFirstBoundaryUnit data m j hj ha hs h2 h3 h4 h6 u hprimitive =
      Units.map (algebraMap Q Q[T;T⁻¹]).toMonoidHom (arithmeticStartOneQuotient W ha π m) *
        terminalPolygonFirstBoundaryUnit data m j hj ha hs h2 h3 h4 h6 u hprimitive := by
  simp only [fixedTerminalPolygonFirstBoundaryUnit, terminalPolygonFirstBoundaryUnit,
    NodalFiber.unitNormalizedFirstUnit, arithmeticFixedTerminalUnit, mul_inv_rev,
    inv_inv, map_mul, mul_assoc]
  rfl

omit hprimitive in
/-- Changing the target smoothing leaves the entire second parameter unchanged. -/
theorem fixedTerminalPolygonSecondBoundaryUnit_eq :
    fixedTerminalPolygonSecondBoundaryUnit data m j hj ha hs h2 h3 h4 h6 =
      terminalPolygonSecondBoundaryUnit data m j hj ha hs h2 h3 h4 h6 := rfl

end FLT.Mazur.WeierstrassDividedDepth
