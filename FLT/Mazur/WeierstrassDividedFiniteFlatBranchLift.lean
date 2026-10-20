/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchScheme
public import FLT.Mazur.WeierstrassDividedVerticalRefinement
public import FLT.Mazur.WeierstrassDividedTangentBranchTerminalFiber
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput

/-!
# Strict-branch tangent outputs in the actual finite model

Use arbitrary flat two-input sources and insert the constructed divided
output into the same finite model. Its original contraction is the exact
tangent output, including when that output is originally singular.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsBezout R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a2 b4' b6' : R)
  (h2 : W.a₂ = π ^ (start + j) * a2)
  (h4' : (data ⟨j, Nat.lt_succ_of_le hj⟩).b4 = π ^ (start + j) * b4')
  (h6' : (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 = π ^ (start + j) * b6')
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
variable (a c : Coordinate W (π ^ (start + j))
  (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
  (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 →ₐ[R] S)
local notation "B" => DividedTangentBranchRing W s (d).b3 (d).b4 (d).b6 a c
local notation "e" => dividedTangentBranchRestriction W s (d).b3 (d).b4 (d).b6 a c
local notation "v" => dividedTangentBranchLift W s (d).b3 (d).b4 (d).b6 a c
  a2 b4' b6' (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2
  (d).factor3 (d).factor4 (d).factor6 h4' h6'

/-- The constructed branch output in the same entire finite model as both inputs. -/
def finiteFlatBranchLift : Spec (.of B) ⟶ finiteGlobalModel hπ data j hj :=
  v ≫ finiteSecantDividedChart hπ data j hj

/-- Its original contraction is the actual tangent output on this genuine branch domain. -/
@[reassoc] theorem finiteFlatBranchLift_contraction :
    finiteFlatBranchLift hπ data j hj a2 b4' b6' h2 h4' h6' a c ≫
        finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
        dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 := by
  rw [finiteFlatBranchLift, Category.assoc, finiteSecantDividedChart_contraction]
  exact dividedTangentBranchLift_contraction ..

/-- The output retains the original coefficient point on the entire branch domain. -/
@[reassoc] theorem finiteFlatBranchLift_structure :
    finiteFlatBranchLift hπ data j hj a2 b4' b6' h2 h4' h6' a c ≫
        finiteGlobalStructure hπ data j hj = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteFlatBranchLift, Category.assoc, finiteSecantDividedChart_structure]
  exact specAlgHom_structure _

local notation "out" => dividedTangentBranchOutput W s (d).b3 (d).b4 (d).b6 a c
  a2 b4' b6' (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2
  (d).factor3 (d).factor4 (d).factor6 h4' h6'
local notation "δ" => out (verticalDerivative W s (d).b3 (d).b4 (d).b6)
local notation "i" => PrincipalAffineRefinement.inclusion δ
local notation "F" => finiteFlatBranchLift hπ data j hj a2 b4' b6' h2 h4' h6' a c
local notation "base" => finiteGlobalStructure hπ data j hj
variable [IsNoetherianRing R]

/-- The derivative neighborhood gives smooth output over every flat input algebra. -/
theorem finiteFlatBranchLift_range_smooth : Set.range (i ≫ F) ⊆ (base).smoothLocus := by
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq (finiteSecantDividedChart hπ data j hj) base
  simp only [finiteSecantDividedChart_structure] at h
  apply h.ge
  exact dividedVerticalRefinement_range_smooth W s (d).b3 (d).b4 (d).b6 out ⟨z, rfl⟩

/-- Unit terminal constant covers the entire special fiber with smooth outputs. -/
theorem finiteFlatBranchLift_terminal_smooth (p : PrimeSpectrum B)
    (hp : algebraMap R B s ∈ p.asIdeal) (hp3 : algebraMap R B (d).b3 ∈ p.asIdeal)
    (hb6 : IsUnit b6') : F p ∈ (base).smoothLocus := by
  have hr : p ∈ Set.range i := by
    rw [PrincipalAffineRefinement.range_inclusion]
    exact dividedTangentBranch_terminalFiber_mem W s (d).b3 (d).b4 (d).b6 a c a2 b4' b6'
      (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2 (d).factor3 (d).factor4
      (d).factor6 h4' h6' p hp hp3 hb6
  obtain ⟨z, hz⟩ := hr
  exact finiteFlatBranchLift_range_smooth hπ data j hj a2 b4' b6' h2 h4' h6' a c
    ⟨z, congrArg F hz⟩

end FLT.Mazur.WeierstrassDividedDepth
