/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteDeeperBranchPartial

/-!
# Terminal coverage for the actual doubled-depth output

The horizontal derivative neighborhood covers every branch prime where the
input scale and final fourth quotient vanish and the final constant is a
unit. Thus these nonterminal inputs have smooth outputs in the chosen entire
finite model, without assumptions about either output coordinate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (d : Data W π k) (hl : start + j = k + k)
  (h2 : W.a₂ = 0)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "out" => depthBranchOutput hπ d e hl h2 a c
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "F" => finiteDeeperBranchLift hπ data j hj d hl h2 a c
local notation "δ" => finiteDeeperBranchPartial hπ data j hj d hl h2 a c 0
local notation "i" => PrincipalAffineRefinement.inclusion δ

omit [IsBezout R] in
/-- The horizontal neighborhood covers the entire indicated terminal branch fiber. -/
theorem finiteDeeperBranch_terminal_range (p : PrimeSpectrum B)
    (hs : algebraMap R B (π ^ k) ∈ p.asIdeal)
    (h4 : algebraMap R B (e).b4 ∈ p.asIdeal)
    (ha : IsUnit W.a₁) (h6 : IsUnit (e).b6) : p ∈ Set.range i := by
  have hs' : algebraMap R B (π ^ (start + j)) ∈ p.asIdeal := by
    rw [hl, pow_add, map_mul]
    exact p.asIdeal.mul_mem_right _ hs
  have h2' : algebraMap R B W.a₂ ∈ p.asIdeal := by rw [h2, map_zero]; exact Ideal.zero_mem _
  exact dividedOutput_terminal_horizontal_range W (π ^ (start + j))
    (e).b3 (e).b4 (e).b6 out p hs' h2' h4 ha h6

variable [IsNoetherianRing R]

/-- Every covered terminal branch prime maps to the actual finite model's smooth locus. -/
theorem finiteDeeperBranch_terminal_smooth (p : PrimeSpectrum B)
    (hs : algebraMap R B (π ^ k) ∈ p.asIdeal)
    (h4 : algebraMap R B (e).b4 ∈ p.asIdeal)
    (ha : IsUnit W.a₁) (h6 : IsUnit (e).b6) : F p ∈ (base).smoothLocus := by
  obtain ⟨z, rfl⟩ := finiteDeeperBranch_terminal_range hπ data j hj d hl h2 a c p hs h4 ha h6
  exact finiteDeeperBranchPartial_range_smooth hπ data j hj d hl h2 a c 0 ⟨z, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
