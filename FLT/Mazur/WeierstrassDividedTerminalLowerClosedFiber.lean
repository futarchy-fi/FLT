/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalLowerCoordinates
public import FLT.Mazur.WeierstrassDividedLowerDepthClosedFiber

/-!
# Strict terminal lowering cannot supply punctured closed-fiber inputs

Both lower coordinates vanish at every closed-fiber terminal point. In
particular a positive retained depth and a sum fitting in the final stage
force a nonpunctured terminal contraction. Sum-depth punctured coverage at
these lower coordinates therefore does not cover any new terminal input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (l : ℕ) (hl : l ≤ j)
local notation "d" => data ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "B" => Coordinate W (π ^ (start + j)) (e).b3 (e).b4 (e).b6
local notation "low" => terminalLowerCoordinates hπ data j hj l hl

/-- A strict terminal contraction kills both coordinates at every closed-fiber prime. -/
theorem terminalLowerCoordinates_closedFiber (hlt : l < j) (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    x W (π ^ (start + l)) (d).b3 (d).b4 (d).b6 ∈ (low p).asIdeal ∧
      y W (π ^ (start + l)) (d).b3 (d).b4 (d).b6 ∈ (low p).asIdeal :=
  lowerDepthClosedFiber_coordinates hπ d e
    (by change start + l < start + j; omega) p hp

/-- The same strict terminal contraction has zero vertical derivative on the closed fiber. -/
theorem terminalLowerCoordinates_closedFiber_vertical (hlt : l < j) (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    verticalDerivative W (π ^ (start + l)) (d).b3 (d).b4 (d).b6 ∈ (low p).asIdeal :=
  lowerDepthClosedFiber_vertical hπ d e
    (by change start + l < start + j; omega) p hp

/-- A punctured lower terminal input on the closed fiber must retain the final depth. -/
theorem terminalLowerCoordinates_punctured_depth (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal)
    (hx : x W (π ^ (start + l)) (d).b3 (d).b4 (d).b6 ∉ (low p).asIdeal) : l = j := by
  by_contra h
  exact hx (terminalLowerCoordinates_closedFiber hπ data j hj l hl (by omega) p hp).1

/-- A positive depth sum fitting in the stage excludes punctured lower terminal inputs. -/
theorem terminalLowerCoordinates_sumDepth_not_punctured {k : ℕ} (hk : 0 < k)
    (hsum : k + l ≤ j) (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) :
    x W (π ^ (start + l)) (d).b3 (d).b4 (d).b6 ∈ (low p).asIdeal :=
  (terminalLowerCoordinates_closedFiber hπ data j hj l hl (by omega) p hp).1

end FLT.Mazur.WeierstrassDividedDepth
