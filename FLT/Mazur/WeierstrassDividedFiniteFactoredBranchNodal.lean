/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteFactoredBranchTerminal
public import FLT.Mazur.WeierstrassDividedNodalDepthAvailability

/-!
# Smooth doubled-depth branch outputs from the original node conditions

The exact node depth supplies terminal coefficient invertibility and
vanishing. Every special-fiber prime of the strict branch is therefore
covered by the constructed horizontal smooth neighborhood. The second
coefficient need only be divisible by the input scale.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k n : ℕ} (D : SplitNodeDepth W π (4 * k))
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hj : k + k ≤ n) (d : Data W π k) (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "e" => data ⟨k + k, Nat.lt_succ_of_le hj⟩
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "base" => finiteGlobalStructure hπ data (k + k) hj
local notation "F" => finiteFactoredBranchLift hπ data (k + k) hj d (Nat.zero_add _) a2 h2 a c
local notation "δ" => finiteFactoredBranchPartial hπ data (k + k) hj d (Nat.zero_add _) a2 h2 a c 0

omit [IsBezout R] in
/-- Original split-node coefficients give coverage of every actual special-fiber branch prime. -/
theorem finiteFactoredBranch_nodal_range (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    p ∈ Set.range (PrincipalAffineRefinement.inclusion δ) := by
  have hk : k ≠ 0 := by have h := D.depth_pos; omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hs : algebraMap R B (π ^ k) ∈ p.asIdeal := by
    simp only [hr, pow_succ, map_mul]
    exact p.asIdeal.mul_mem_left _ hp
  have h4 := (nodalDepth_linear_mem hπ D.maximalIdeal_eq e
    (by omega : 2 * (0 + (k + k)) ≤ 4 * k) D.a₃_mem D.a₄_mem).2
  rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at h4
  obtain ⟨b, hb⟩ := h4
  have h4' : algebraMap R B (e).b4 ∈ p.asIdeal := by
    rw [hb, map_mul]
    exact p.asIdeal.mul_mem_right _ hp
  exact finiteFactoredBranch_terminal_range hπ data (k + k) hj d (Nat.zero_add _) a2 h2
    a c p hs h4' D.a₁_unit (nodalDepth_constant_isUnit D.maximalIdeal_eq e
      (by change 2 * (0 + (k + k)) = 4 * k; omega) D.a₆_not_mem)

variable [IsNoetherianRing R]

/-- The doubled-depth output is smooth on the entire special fiber of this branch. -/
theorem finiteFactoredBranch_nodal_smooth (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) : F p ∈ (base).smoothLocus := by
  obtain ⟨z, rfl⟩ := finiteFactoredBranch_nodal_range D data hj d a2 h2 a c p hp
  exact finiteFactoredBranchPartial_range_smooth hπ data (k + k) hj d (Nat.zero_add _)
    a2 h2 a c 0 ⟨z, rfl⟩

/-- The terminal model and every required intermediate datum can all be constructed from D. -/
theorem finiteFactoredBranch_constructed_nodal_smooth (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    finiteFactoredBranchLift hπ (splitNodeDoubledFamily D) (k + k) le_rfl d
      (Nat.zero_add _) a2 h2 a c p ∈
        (finiteGlobalStructure hπ (splitNodeDoubledFamily D) (k + k) le_rfl).smoothLocus :=
  finiteFactoredBranch_nodal_smooth D (splitNodeDoubledFamily D) le_rfl d a2 h2 a c p hp

end FLT.Mazur.WeierstrassDividedDepth
