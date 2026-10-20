/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTangentBranchSmooth
public import FLT.Mazur.WeierstrassDividedTangentBranchTerminalFiber

/-!
# Terminal branch outputs are smooth in the entire finite model

The actual branch fiber is covered by the derivative neighborhood, so its
constructed outputs land in the full finite smooth locus even when their
original cubic images are singular.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a2 b4' b6' : R)
  (h2 : W.a₂ = π ^ (start + j) * a2)
  (h4' : (data ⟨j, Nat.lt_succ_of_le hj⟩).b4 = π ^ (start + j) * b4')
  (h6' : (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 = π ^ (start + j) * b6')
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "a" => dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "B" => DividedTangentBranchRing W s (d).b3 (d).b4 (d).b6 a c
local notation "e" => dividedTangentBranchRestriction W s (d).b3 (d).b4 (d).b6 a c
local notation "v" => dividedTangentBranchLift W s (d).b3 (d).b4 (d).b6 a c
  a2 b4' b6' (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2
  (d).factor3 (d).factor4 (d).factor6 h4' h6'

local notation "out" => dividedTangentBranchOutput W s (d).b3 (d).b4 (d).b6 a c
  a2 b4' b6' (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2
  (d).factor3 (d).factor4 (d).factor6 h4' h6'
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

local notation "δ" => finiteTangentBranchDerivative hπ data j hj a2 b4' b6' h2 h4' h6'
local notation "i" => PrincipalAffineRefinement.inclusion δ
local notation "F" => finiteTangentBranchLift hπ data j hj a2 b4' b6' h2 h4' h6'

omit [IsBezout R] [IsNoetherianRing R] in
/-- The entire terminal branch fiber is contained in the constructed smooth neighborhood. -/
theorem finiteTangentBranch_terminal_range (p : PrimeSpectrum B)
    (hp : algebraMap R B s ∈ p.asIdeal) (hp3 : algebraMap R B (d).b3 ∈ p.asIdeal)
    (hb6 : IsUnit b6') : p ∈ Set.range i := by
  rw [PrincipalAffineRefinement.range_inclusion]
  exact dividedTangentBranch_terminalFiber_mem W s (d).b3 (d).b4 (d).b6 a c a2 b4' b6'
    (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2 (d).factor3 (d).factor4
    (d).factor6 h4' h6' p hp hp3 hb6

/-- Every terminal strict-branch output is smooth in the same actual finite model. -/
theorem finiteTangentBranch_terminal_smooth (p : PrimeSpectrum B)
    (hp : algebraMap R B s ∈ p.asIdeal) (hp3 : algebraMap R B (d).b3 ∈ p.asIdeal)
    (hb6 : IsUnit b6') : F p ∈ U := by
  obtain ⟨z, hz⟩ := finiteTangentBranch_terminal_range hπ data j hj a2 b4' b6'
    h2 h4' h6' p hp hp3 hb6
  exact finiteTangentBranchRefinement_range_smooth hπ data j hj a2 b4' b6' h2 h4' h6'
    ⟨z, congrArg F hz⟩

end FLT.Mazur.WeierstrassDividedDepth
