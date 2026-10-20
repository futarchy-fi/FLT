/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteSmoothSecant
public import FLT.Mazur.WeierstrassDividedTripleSecantCases
public import FLT.Mazur.WeierstrassDividedTripleTangentBranchCoverage

/-!
# Actual smooth outputs cover triple-depth secants with smooth vertical inputs

The residue classification selects either the constructed smooth secant
open or one of the two actual finite-model branch outputs. All outputs
use the same original finite model and retain the source coefficient point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "T" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "r" => nodalSecondShear D (start + k)
local notation "a'" => branchNegativeInput W s (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W s (d).b3 (d).b4 (d).b6 c
local notation "N" => DividedShearBranchOverlap W s (d).b3 (d).b4 (d).b6 r a' c'
local notation "B" => DividedShearBranchOverlap W s (d).b3 (d).b4 (d).b6 r c a
local notation "base" => finiteGlobalStructure D.uniformizer_ne_zero data k hk

/-- Every triple-depth secant with vertical-smooth inputs has a constructed smooth local output. -/
theorem tripleSecant_smooth_output_cover (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal) :
    p ∈ finiteSmoothSecantOpen data k hk a c ∨
      (∃ q : PrimeSpectrum N,
        PrimeSpectrum.comap (algebraMap S N) q = PrimeSpectrum.comap (algebraMap S T) p ∧
        algebraMap R N π ∈ q.asIdeal ∧
          tripleNegativeBranchOutput D data hk a c q ∈ (base).smoothLocus) ∨
      (∃ q : PrimeSpectrum B,
        PrimeSpectrum.comap (algebraMap S B) q = PrimeSpectrum.comap (algebraMap S T) p ∧
        algebraMap R B π ∈ q.asIdeal ∧
          tripleBranchCommonOutput D data hk c a q ∈ (base).smoothLocus) := by
  let p₀ := PrimeSpectrum.comap (algebraMap S T) p
  have hp₀ : algebraMap R S π ∈ p₀.asIdeal := by
    change algebraMap S T (algebraMap R S π) ∈ p.asIdeal
    rwa [← IsScalarTower.algebraMap_apply]
  rcases tripleSecant_prime_three_cases D d a c p hp ha hc with hn | hb | hs
  · exact Or.inr (Or.inl (tripleNegativeBranchOutput_covers D data hk a c p₀ hp₀ hn))
  · exact Or.inr (Or.inr (tripleBranchCommonOutput_covers D data hk c a p₀ hp₀ hb))
  · left
    apply finiteSmoothSecantOpen_mem data k hk a c p _ hs
    have hk0 : start + k ≠ 0 := by have h := D.depth_pos; omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp only [hm, pow_succ, map_mul]
    exact p.asIdeal.mul_mem_left _ hp

end FLT.Mazur.WeierstrassDividedDepth
