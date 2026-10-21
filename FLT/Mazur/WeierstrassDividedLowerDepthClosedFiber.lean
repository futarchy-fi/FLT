/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedOlderCoordinates
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Strictly lower common coordinates on the closed fiber

A strict depth transition sends both coordinates and the vertical derivative
to zero in the residue field. This applies to the actual whole retained older
chart, so vertical smoothness cannot be inferred from its resolved smoothness.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k < l)
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ l) e.b3 e.b4 e.b6
local notation "f" => depthTransition π k l hπ hkl.le W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
  d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6

/-- Strict lowering kills both divided coordinates on the closed fiber. -/
theorem lowerDepthClosedFiber_coordinates (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    f (x W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal ∧
      f (y W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal := by
  have hs : algebraMap R B (π ^ (l - k)) ∈ p.asIdeal := by
    rw [map_pow]
    exact p.asIdeal.pow_mem_of_mem hp _ (by omega)
  constructor
  · rw [depthTransition_x]
    exact p.asIdeal.mul_mem_right _ hs
  · rw [depthTransition_y]
    exact p.asIdeal.mul_mem_right _ hs

/-- The contracted vertical derivative also vanishes, even for a smooth deeper input. -/
theorem lowerDepthClosedFiber_vertical (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    f (verticalDerivative W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal := by
  obtain ⟨hx, hy⟩ := lowerDepthClosedFiber_coordinates hπ d e hkl p hp
  have h3 : algebraMap R B d.b3 ∈ p.asIdeal := by
    rw [depth_coefficient_factor π k l hπ hkl.le d.factor3 e.factor3, map_mul, map_pow]
    exact p.asIdeal.mul_mem_right _ (p.asIdeal.pow_mem_of_mem hp _ (by omega))
  rw [verticalDerivative_eq, map_add, map_add, map_mul, map_mul, map_ofNat,
    AlgHom.commutes, AlgHom.commutes]
  exact p.asIdeal.add_mem
    (p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hy) (p.asIdeal.mul_mem_left _ hx)) h3

variable {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (l : ℕ) (hl : l < j) (k : ℕ) (hkl : k < l)
local notation "idx" => retainedOlderFormulaIndex j l hl
local notation "d₀" => data ⟨k, by omega⟩
local notation "d₁" => data ⟨l, by omega⟩
local notation "old" => retainedOlderFormulaCoordinates hπ data j hj l hl
local notation "low" => retainedOlderLowerCoordinates hπ data j hj l hl k hkl.le
local notation "B₁" => WeierstrassDilatation.Coordinate W (π ^ (start + l))
  (d₁).b3 (d₁).b4 (d₁).b6

/-- Whole retained older charts have vanishing lower coordinates at their closed-fiber points. -/
theorem retainedOlderLowerCoordinates_closedFiber
    (p : globalIntegralAtlasObject data j hj idx)
    (hp : algebraMap R B₁ π ∈ (old p).asIdeal) :
    x W (π ^ (start + k)) (d₀).b3 (d₀).b4 (d₀).b6 ∈ (low p).asIdeal ∧
      y W (π ^ (start + k)) (d₀).b3 (d₀).b4 (d₀).b6 ∈ (low p).asIdeal :=
  lowerDepthClosedFiber_coordinates hπ d₀ d₁
    (by change start + k < start + l; omega) (old p) hp

/-- No strict common-depth contraction of a closed-fiber retained input is vertically smooth. -/
theorem retainedOlderLowerCoordinates_closedFiber_vertical
    (p : globalIntegralAtlasObject data j hj idx)
    (hp : algebraMap R B₁ π ∈ (old p).asIdeal) :
    verticalDerivative W (π ^ (start + k)) (d₀).b3 (d₀).b4 (d₀).b6 ∈ (low p).asIdeal :=
  lowerDepthClosedFiber_vertical hπ d₀ d₁
    (by change start + k < start + l; omega) (old p) hp

end FLT.Mazur.WeierstrassDividedDepth
