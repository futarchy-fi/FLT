/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBranchDivisibility
public import FLT.Mazur.WeierstrassDividedTangentBranchResidue

/-!
# Construct branch ordinates at each input's own depth

Doubled-depth coefficient data and the actual equation construct the
ordinate divided by its own scale on the complementary branch open.
Only an input denominator is assumed invertible.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + k)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "W'" => W.map (algebraMap R S)
variable (hc : IsUnit (a (y W (π ^ k) d.b3 d.b4 d.b6) +
  algebraMap R S W.a₁ * a (x W (π ^ k) d.b3 d.b4 d.b6) + algebraMap R S d.b3))

/-- A constructed quotient of the input ordinate by its own depth scale. -/
def ownBranchOrdinate : S :=
  tangentBranchOrdinate W' (algebraMap R S d.b3) 0 (algebraMap R S e.b4)
    (s * algebraMap R S e.b6) x₁ y₁ hc

omit [IsDomain R] in
/-- Its denominator relation retains the input's uncontracted abscissa. -/
theorem ownBranchOrdinate_denominator :
    ownBranchOrdinate d e a hc *
        (y₁ + algebraMap R S W.a₁ * x₁ + algebraMap R S d.b3) =
      x₁ ^ 3 + algebraMap R S e.b4 * x₁ + s * algebraMap R S e.b6 := by
  simpa only [ownBranchOrdinate, WeierstrassCurve.map_a₁, zero_mul, add_zero] using
    tangentBranchOrdinate_denominator
    W' (algebraMap R S d.b3) 0 (algebraMap R S e.b4)
    (s * algebraMap R S e.b6) x₁ y₁ hc

include hπ h2 in
/-- Divisibility follows from the input equation and doubled-depth coefficients. -/
theorem ownBranchOrdinate_scale : s * ownBranchOrdinate d e a hc = y₁ := by
  apply tangentBranchOrdinate_mul W' s (algebraMap R S d.b3) (algebraMap R S d.b4)
    (algebraMap R S d.b6) 0 (algebraMap R S e.b4)
    (s * algebraMap R S e.b6) x₁ y₁ hc
  · simp only [WeierstrassCurve.map_a₂, h2, map_zero, mul_zero]
  · rw [branch_depth_factor4 hπ d e, map_mul]
  · rw [branch_depth_first_factor6 hπ d e, map_mul, map_mul]
  · exact equation_map W (π ^ k) d.b3 d.b4 d.b6 a

end FLT.Mazur.WeierstrassDividedDepth
