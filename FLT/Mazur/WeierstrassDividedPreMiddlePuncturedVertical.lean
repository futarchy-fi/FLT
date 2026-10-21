/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPreMiddleBranchDichotomy
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Punctured pre-middle inputs have nonzero vertical derivative

The two residue branches give opposite unit multiples of the abscissa.
This uses no characteristic restriction and no flatness of the input algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {k m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "α" => algebraMap R S W.a₁

include D in
/-- Every punctured closed-fiber input in the pre-middle range is vertically nonsingular. -/
theorem preMiddleInput_vertical_not_mem (hk : 0 < k) (hm : 2 * k < m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal) (hx : x₁ ∉ p.asIdeal) :
    a (verticalDerivative W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal := by
  intro hδ
  have h3 := preMiddleInput_b3_mem D d hm p hp
  have hd : 2 * y₁ + α * x₁ ∈ p.asIdeal := by
    rw [verticalDerivative_eq, map_add, map_add, map_mul, map_mul, map_ofNat,
      AlgHom.commutes, AlgHom.commutes] at hδ
    simpa only [add_sub_cancel_right] using p.asIdeal.sub_mem hδ h3
  apply hx
  apply (p.asIdeal.unit_mul_mem_iff_mem (D.a₁_unit.map (algebraMap R S))).mp
  rcases preMiddleInput_branch_dichotomy D d a hk hm p hp with hy | hy
  · simpa only [add_sub_cancel_left] using
      p.asIdeal.sub_mem hd (p.asIdeal.mul_mem_left 2 hy)
  · have hn : y₁ + α * x₁ ∈ p.asIdeal := by
      simpa only [dividedTangentBranchFactor, add_sub_cancel_right] using
        p.asIdeal.sub_mem hy h3
    convert p.asIdeal.sub_mem (p.asIdeal.mul_mem_left 2 hn) hd using 1
    ring

end FLT.Mazur.WeierstrassDividedDepth
