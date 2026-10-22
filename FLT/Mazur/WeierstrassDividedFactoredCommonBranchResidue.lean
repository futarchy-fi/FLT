/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactoredCommonBranchOrdinate

/-!
# Residues of branch ordinates with the quadratic term retained

Specializing the full denominator relation keeps the quadratic quotient.
The original ordinate still vanishes when its common scale vanishes.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation IsLocalRing
set_option quotPrecheck false
variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} {k l : ℕ}
  (e : Data W π l) (ee : CommonBranchData e k) (b2 : R)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
  (hc : IsUnit (c (y W (π ^ l) e.b3 e.b4 e.b6) +
    algebraMap R S W.a₁ * c (x W (π ^ l) e.b3 e.b4 e.b6) + algebraMap R S e.b3))
  (ρ : S →ₐ[R] K)

local notation "x₁" => c (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₁" => c (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "q" => factoredCommonBranchOrdinate e ee b2 c hc

include ee hc in
/-- The constructed branch ordinate forces the original ordinate to vanish. -/
theorem factoredCommonBranchOrdinate_residue_ordinate (hkl : k ≤ l)
    (h2 : W.a₂ = π ^ k * b2) (hs : algebraMap R K (π ^ k) = 0) : ρ y₁ = 0 := by
  have h := congrArg ρ (factoredCommonBranchOrdinate_scale e ee b2 c hc hkl h2)
  simpa only [map_mul, AlgHom.commutes, hs, zero_mul] using h.symm

/-- After cancelling the input abscissa, the finite quadratic quotient remains explicit. -/
theorem factoredCommonBranchOrdinate_residue_leading
    (τ : K) (ht : algebraMap R K (π ^ (l - k)) = τ)
    (hy : ρ y₁ = 0) (h3 : algebraMap R K e.b3 = 0)
    (h4 : algebraMap R K ee.b4 = 0) (h6 : algebraMap R K ee.b6 = 0)
    (hx : ρ x₁ ≠ 0) :
    algebraMap R K W.a₁ * ρ q = τ * (ρ x₁) ^ 2 + algebraMap R K b2 * ρ x₁ := by
  simp only [map_pow] at ht
  have h := congrArg ρ (factoredCommonBranchOrdinate_denominator e ee b2 c hc)
  simp only [map_mul, map_add, map_pow, AlgHom.commutes, ht, hy, h3, h4, h6,
    zero_mul, zero_add, add_zero] at h
  apply (mul_right_inj' hx).mp
  linear_combination h

end FLT.Mazur.WeierstrassDividedDepth
