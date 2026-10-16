/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberUnitScalingBoundary
public import FLT.Mazur.WeierstrassDilatationCoherentTerminalPolygon
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureUnits

/-!
# The original terminal boundaries in normalized polygon coordinates

The actual original Laurent evaluations determine the full corrected boundary
parameters. The opposite label uses the first factor divided by the coherent
smoothing unit; the small label keeps the second factor without modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
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
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "c" => arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "v" => arithmeticCoherentTerminalUnit π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive m
local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6
local notation "P" => coherentTerminalPolygonIso π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive m

/-- The corrected full first-factor unit at the original opposite terminal boundary. -/
def terminalPolygonFirstBoundaryUnit : Q[T;T⁻¹]ˣ :=
  NodalFiber.unitNormalizedFirstUnit c v (E true) (by
    simpa only [↓reduceIte] using
      terminalArithmeticSelected_unit data m j hj ha hs h2 h3 h4 h6 true)

omit hprimitive in
/-- The full original second-factor unit at the small terminal boundary. -/
def terminalPolygonSecondBoundaryUnit : Q[T;T⁻¹]ˣ :=
  (terminalArithmeticSelected_unit data m j hj ha hs h2 h3 h4 h6 false).unit

/-- The exact change from the original Laurent parameter to the polygon boundary parameter. -/
def terminalPolygonBoundaryParameter (opposite : Bool) :
    PolygonSmoothing.branchTorus Q ⟶ PolygonSmoothing.branchTorus Q :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
    (if opposite then terminalPolygonFirstBoundaryUnit data m j hj
      ha hs h2 h3 h4 h6 u hprimitive
    else terminalPolygonSecondBoundaryUnit data m j hj ha hs h2 h3 h4 h6)).toRingHom)

/-- The opposite terminal boundary retains its full corrected first-factor parameter. -/
@[reassoc] theorem terminalPolygon_first_boundary :
    Spec.map (CommRingCat.ofHom (E true).toRingHom) ≫ (P).hom =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
        (terminalPolygonFirstBoundaryUnit data m j hj ha hs h2 h3 h4 h6 u hprimitive)).toRingHom) ≫
          PolygonSmoothing.leftBranchOpen Q (parameter R π m) := by
  exact NodalFiber.unitSmoothingIso_first_boundary c (parameter R π m) v
    (arithmeticCoherentTerminalUnit_spec π W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
      ha hs₂ h2 h3 h4 h6 u hprimitive m) (E true) _

/-- The small terminal boundary keeps the full original second-factor Laurent parameter. -/
@[reassoc] theorem terminalPolygon_second_boundary :
    Spec.map (CommRingCat.ofHom (E false).toRingHom) ≫ (P).hom =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
        (terminalPolygonSecondBoundaryUnit data m j hj ha hs h2 h3 h4 h6)).toRingHom) ≫
          PolygonSmoothing.rightBranchOpen Q (parameter R π m) := by
  exact NodalFiber.unitSmoothingIso_second_boundary c (parameter R π m) v
    (arithmeticCoherentTerminalUnit_spec π W s (Data.b3 d) (Data.b4 d) (Data.b6 d)
      ha hs₂ h2 h3 h4 h6 u hprimitive m) (E false) _

/-- Both original boundary labels retain their actual normalized Laurent parameter maps. -/
@[reassoc] theorem terminalPolygon_boundary (opposite : Bool) :
    Spec.map (CommRingCat.ofHom (E opposite).toRingHom) ≫ (P).hom =
      terminalPolygonBoundaryParameter data m j hj ha hs h2 h3 h4 h6 u hprimitive opposite ≫
        (if opposite then PolygonSmoothing.leftBranchOpen Q (parameter R π m)
        else PolygonSmoothing.rightBranchOpen Q (parameter R π m)) := by
  cases opposite
  · exact terminalPolygon_second_boundary data m j hj ha hs h2 h3 h4 h6 u hprimitive
  · exact terminalPolygon_first_boundary data m j hj ha hs h2 h3 h4 h6 u hprimitive

end FLT.Mazur.WeierstrassDividedDepth
