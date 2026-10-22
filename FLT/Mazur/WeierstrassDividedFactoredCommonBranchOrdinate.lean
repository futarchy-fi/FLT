/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCommonBranchOrdinate

/-!
# Common-scale ordinates with a factored second coefficient

Retain the quadratic term in the explicit quotient of the branch equation.
The second coefficient needs only a finite power factorization, as supplied
by nodalSecondShear; it need not vanish identically.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k l : ℕ}
  (d : Data W π l) (q : CommonBranchData d k) (b2 : R)
  (a : Coordinate W (π ^ l) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "t" => algebraMap R S (π ^ (l - k))
local notation "x₁" => a (x W (π ^ l) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ l) d.b3 d.b4 d.b6)
local notation "f" => y₁ + algebraMap R S W.a₁ * x₁ + algebraMap R S d.b3
variable (hc : IsUnit (a (y W (π ^ l) d.b3 d.b4 d.b6) +
  algebraMap R S W.a₁ * a (x W (π ^ l) d.b3 d.b4 d.b6) + algebraMap R S d.b3))

/-- The common-scale ordinate is an explicit quotient by the unit branch factor. -/
def factoredCommonBranchOrdinate : S :=
  (t * x₁ ^ 3 + algebraMap R S b2 * x₁ ^ 2 +
    algebraMap R S q.b4 * x₁ + algebraMap R S q.b6) * ↑hc.unit⁻¹

/-- Its denominator relation uses the full own-depth abscissa. -/
theorem factoredCommonBranchOrdinate_denominator :
    factoredCommonBranchOrdinate d q b2 a hc * f =
      t * x₁ ^ 3 + algebraMap R S b2 * x₁ ^ 2 + algebraMap R S q.b4 * x₁ + algebraMap R S q.b6 := by
  rw [factoredCommonBranchOrdinate, mul_assoc, hc.val_inv_mul, mul_one]

/-- The original equation constructs common-scale divisibility of the ordinate. -/
theorem factoredCommonBranchOrdinate_scale (hkl : k ≤ l) (h2 : W.a₂ = π ^ k * b2) :
    s * factoredCommonBranchOrdinate d q b2 a hc = y₁ := by
  apply hc.mul_left_inj.mp
  rw [mul_assoc, factoredCommonBranchOrdinate_denominator]
  have he := equation_map W (π ^ l) d.b3 d.b4 d.b6 a
  have hs : s * t = algebraMap R S (π ^ l) := by
    rw [← map_mul, ← pow_add, Nat.add_sub_of_le hkl]
  have h4 : algebraMap R S d.b4 = s * algebraMap R S q.b4 := by
    rw [q.factor4, map_mul]
  have h6 : algebraMap R S d.b6 = s * algebraMap R S q.b6 := by
    rw [q.factor6, map_mul]
  rw [h2, map_mul, h4, h6, ← hs] at he
  linear_combination -he

end FLT.Mazur.WeierstrassDividedDepth
