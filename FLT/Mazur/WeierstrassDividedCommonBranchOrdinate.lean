/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCommonBranchData
public import FLT.Mazur.WeierstrassDividedQuotientBranchOrdinate

/-!
# Construct branch ordinates at a common shallower scale

Use the original divided equation and coefficient quotients to divide the
ordinate at depth l by the scale at depth k. No ordinate divisibility is
assumed, and the deeper input retains its entire own-depth coordinates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k l : ℕ}
  (d : Data W π l) (q : CommonBranchData d k)
  (a : Coordinate W (π ^ l) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "t" => algebraMap R S (π ^ (l - k))
local notation "x₁" => a (x W (π ^ l) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ l) d.b3 d.b4 d.b6)
local notation "f" => y₁ + algebraMap R S W.a₁ * x₁ + algebraMap R S d.b3
variable (hc : IsUnit (a (y W (π ^ l) d.b3 d.b4 d.b6) +
  algebraMap R S W.a₁ * a (x W (π ^ l) d.b3 d.b4 d.b6) + algebraMap R S d.b3))

/-- The common-scale ordinate is an explicit quotient by the unit branch factor. -/
def commonBranchOrdinate : S :=
  (t * x₁ ^ 3 + algebraMap R S q.b4 * x₁ + algebraMap R S q.b6) * ↑hc.unit⁻¹

/-- Its denominator relation uses the full own-depth abscissa. -/
theorem commonBranchOrdinate_denominator :
    commonBranchOrdinate d q a hc * f =
      t * x₁ ^ 3 + algebraMap R S q.b4 * x₁ + algebraMap R S q.b6 := by
  rw [commonBranchOrdinate, mul_assoc, hc.val_inv_mul, mul_one]

/-- The original equation constructs common-scale divisibility of the ordinate. -/
theorem commonBranchOrdinate_scale (hkl : k ≤ l) (h2 : W.a₂ = 0) :
    s * commonBranchOrdinate d q a hc = y₁ := by
  apply hc.mul_left_inj.mp
  rw [mul_assoc, commonBranchOrdinate_denominator]
  have he := equation_map W (π ^ l) d.b3 d.b4 d.b6 a
  have hs : s * t = algebraMap R S (π ^ l) := by
    rw [← map_mul, ← pow_add, Nat.add_sub_of_le hkl]
  have h4 : algebraMap R S d.b4 = s * algebraMap R S q.b4 := by
    rw [q.factor4, map_mul]
  have h6 : algebraMap R S d.b6 = s * algebraMap R S q.b6 := by
    rw [q.factor6, map_mul]
  rw [h2, map_zero, h4, h6, ← hs] at he
  linear_combination -he

end FLT.Mazur.WeierstrassDividedDepth
