/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOwnBranchOrdinate

/-!
# Residues of the constructed own-depth branch ordinate

The input equation forces the positive branch at every closed-fiber point
of the complementary branch open. Its constructed quotient retains the
leading abscissa square after cancelling the punctured input abscissa.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (dd : Data W π (k + k)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (hc : IsUnit (a (y W (π ^ k) d.b3 d.b4 d.b6) +
    algebraMap R S W.a₁ * a (x W (π ^ k) d.b3 d.b4 d.b6) + algebraMap R S d.b3))
  (ρ : S →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "q" => ownBranchOrdinate d dd a hc

include hπ h2 hs dd hc in
/-- On the complementary branch open the own-depth input ordinate vanishes in the residue. -/
theorem ownBranchOrdinate_residue_y : ρ y₁ = 0 := by
  have h := congrArg ρ (ownBranchOrdinate_scale hπ d dd h2 a hc)
  simpa only [map_mul, AlgHom.commutes, hs, zero_mul] using h.symm

include hπ h2 hs dd hc in
/-- The constructed quotient has the exact leading coefficient needed by same-branch addition. -/
theorem ownBranchOrdinate_residue_leading (h3 : algebraMap R K d.b3 = 0)
    (h4 : algebraMap R K dd.b4 = 0) (hx : ρ x₁ ≠ 0) :
    algebraMap R K W.a₁ * ρ q = (ρ x₁) ^ 2 := by
  have hy := ownBranchOrdinate_residue_y hπ d dd h2 a hc ρ hs
  have h := congrArg ρ (ownBranchOrdinate_denominator d dd a hc)
  simp only [map_pow] at hs
  simp only [map_mul, map_add, map_pow, AlgHom.commutes, hy, h3, h4, hs,
    zero_mul, zero_add, add_zero] at h
  apply (mul_right_inj' hx).mp
  linear_combination h

end FLT.Mazur.WeierstrassDividedDepth
