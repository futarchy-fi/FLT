/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleBranchData
public import FLT.Mazur.WeierstrassDividedTangentBranchResidue

/-!
# Construct branch ordinates using only coefficient quotients

The original equation and the two coefficient quotients construct division
by the input scale. No doubled-depth datum is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : Data W π k) (e : BranchQuotientData d) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "W'" => W.map (algebraMap R S)
variable (hc : IsUnit (a (y W (π ^ k) d.b3 d.b4 d.b6) +
  algebraMap R S W.a₁ * a (x W (π ^ k) d.b3 d.b4 d.b6) + algebraMap R S d.b3))

/-- A constructed quotient of the input ordinate by its own depth scale. -/
def quotientBranchOrdinate : S :=
  tangentBranchOrdinate W' (algebraMap R S d.b3) 0 (algebraMap R S e.b4)
    (algebraMap R S e.b6) x₁ y₁ hc

/-- Its denominator relation retains the input's uncontracted abscissa. -/
theorem quotientBranchOrdinate_denominator :
    quotientBranchOrdinate d e a hc *
        (y₁ + algebraMap R S W.a₁ * x₁ + algebraMap R S d.b3) =
      x₁ ^ 3 + algebraMap R S e.b4 * x₁ + algebraMap R S e.b6 := by
  simpa only [quotientBranchOrdinate, WeierstrassCurve.map_a₁, zero_mul, add_zero] using
    tangentBranchOrdinate_denominator
    W' (algebraMap R S d.b3) 0 (algebraMap R S e.b4)
    (algebraMap R S e.b6) x₁ y₁ hc

include h2 in
/-- Divisibility follows from the input equation and the two coefficient quotients. -/
theorem quotientBranchOrdinate_scale : s * quotientBranchOrdinate d e a hc = y₁ := by
  apply tangentBranchOrdinate_mul W' s (algebraMap R S d.b3) (algebraMap R S d.b4)
    (algebraMap R S d.b6) 0 (algebraMap R S e.b4)
    (algebraMap R S e.b6) x₁ y₁ hc
  · simp only [WeierstrassCurve.map_a₂, h2, map_zero, mul_zero]
  · rw [e.factor4, map_mul]
  · rw [e.factor6, map_mul]
  · exact equation_map W (π ^ k) d.b3 d.b4 d.b6 a

end FLT.Mazur.WeierstrassDividedDepth
