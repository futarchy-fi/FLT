/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteFactoredBranchLift
public import FLT.Mazur.WeierstrassDividedNodalDoubledBranchSmooth

/-!
# Smooth finite-model branch outputs above quadruple node depth

Every nodal branch point lies in the actual vertical derivative neighborhood
of the constructed doubled output. Its entire closed fiber therefore maps
into the smooth locus of the chosen finite model.
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
  {W : WeierstrassCurve R} {π : R} {start n k m : ℕ}
  (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (d : Data W π k) (hl : start + j = k + k)
  (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "r" => dividedTangentBranchRestriction W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "v" => factoredDepthBranchLift hπ d e hl a2 h2 a c
local notation "out" => factoredDepthBranchOutput hπ d e hl a2 h2 a c
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

local notation "F" => finiteFactoredBranchLift hπ data j hj d hl a2 h2 a c
local notation "δ" => finiteFactoredBranchDerivative hπ data j hj d hl a2 h2 a c
local notation "i" => PrincipalAffineRefinement.inclusion δ

omit [IsBezout R] in
/-- The constructed derivative neighborhood covers the entire nodal branch fiber. -/
theorem finiteDoubledBranch_deep_range (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) : p ∈ Set.range i := by
  rw [PrincipalAffineRefinement.range_inclusion]
  exact nodalDoubledBranchOutput_vertical_mem D d e hl a2 h2 a c hk hm p hp

variable [IsNoetherianRing R]

/-- Above quadruple depth every constructed branch output is smooth in the entire finite model. -/
theorem finiteDoubledBranch_deep_smooth (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) : F p ∈ U := by
  obtain ⟨z, hz⟩ := finiteDoubledBranch_deep_range D data j hj d hl a2 h2 a c hk hm p hp
  exact finiteFactoredBranchRefinement_range_smooth hπ data j hj d hl a2 h2 a c
    ⟨z, congrArg F hz⟩

end FLT.Mazur.WeierstrassDividedDepth
