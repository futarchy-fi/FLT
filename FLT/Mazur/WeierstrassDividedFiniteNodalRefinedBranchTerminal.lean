/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNodalRefinedBranchLift
public import FLT.Mazur.WeierstrassDividedNodalRefinedBranchTerminalReindex

/-!
# The full intermediate nodal fiber maps into the finite smooth locus

Below quadruple depth, refining by the full residual depth places every
closed-fiber branch point in the explicit derivative neighborhood. The
existing lift therefore has actual smooth output throughout that fiber.
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
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ}
  (D : SplitNodeDepth W π m) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hj : k + r ≤ n) (d : Data W π k)
  (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "e" => data ⟨k + r, Nat.lt_succ_of_le hj⟩
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "res" => dividedTangentBranchRestriction W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "raw" => nodalRefinedBranchReindexedLift
  D d hdepth hrk hrm e (Nat.zero_add _) a2 h2 a c
local notation "out" => nodalRefinedBranchReindexedOutput
  D d hdepth hrk hrm e (Nat.zero_add _) a2 h2 a c
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "U" => (base).smoothLocus

local notation "F" => finiteNodalRefinedBranchLift D hdepth hrk hrm data hj d a2 h2 a c
local notation "δ" => finiteNodalRefinedBranchDerivative D hdepth hrk hrm data hj d a2 h2 a c
local notation "i" => PrincipalAffineRefinement.inclusion δ

omit [IsBezout R] in
/-- Every nodal branch point is reached by the actual intermediate derivative localization. -/
theorem finiteNodalRefinedBranch_terminal_range
    (hm : m < 4 * k) (hr : r = m - 3 * k)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) : p ∈ Set.range i := by
  rw [PrincipalAffineRefinement.range_inclusion]
  exact nodalRefinedBranchReindexedOutput_terminal_mem D d hdepth hrk hrm e
    (Nat.zero_add _) a2 h2 a c hm hr p hp

variable [IsNoetherianRing R]

/-- Every nodal branch output is smooth in the actual entire finite model at intermediate depth. -/
theorem finiteNodalRefinedBranch_terminal_smooth
    (hm : m < 4 * k) (hr : r = m - 3 * k)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) : F p ∈ U := by
  obtain ⟨z, hz⟩ := finiteNodalRefinedBranch_terminal_range
    D hdepth hrk hrm data hj d a2 h2 a c hm hr p hp
  exact finiteNodalRefinedBranchRefinement_range_smooth D hdepth hrk hrm data hj d a2 h2 a c
    ⟨z, congrArg F hz⟩

end FLT.Mazur.WeierstrassDividedDepth
