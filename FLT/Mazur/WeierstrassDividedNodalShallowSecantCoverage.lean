/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteReindexedSmoothSecant
public import FLT.Mazur.WeierstrassDividedNodalSecantCases
public import FLT.Mazur.WeierstrassDividedNodalShallowNegativeBranchOutput

/-!
# Actual smooth outputs cover shallow-depth secants with smooth vertical inputs

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
  nodalShallowBranchCommonOutput nodalShallowNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "N" => DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ a' c'
local notation "B" => DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ c a
local notation "base" => finiteGlobalStructure D.uniformizer_ne_zero
  (start := 0) data (m - 2 * k) hj

/-- Shallow nodal secants with vertical-smooth inputs have actual smooth local outputs. -/
theorem nodalShallowSecant_smooth_output_cover
    (hk : 0 < k) (hlo : 2 * k < m) (hhi : m < 3 * k)
    (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (ha : ((j).comp a) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((j).comp c) (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ finiteReindexedSmoothSecantOpen d a c ∨
      (∃ q : PrimeSpectrum N,
        PrimeSpectrum.comap (algebraMap S N) q = PrimeSpectrum.comap (algebraMap S T) p ∧
        algebraMap R N π ∈ q.asIdeal ∧
          nodalShallowNegativeBranchOutput D hdepth hm data hj d a c q ∈
            (base).smoothLocus) ∨
      (∃ q : PrimeSpectrum B,
        PrimeSpectrum.comap (algebraMap S B) q = PrimeSpectrum.comap (algebraMap S T) p ∧
        algebraMap R B π ∈ q.asIdeal ∧
          nodalShallowBranchCommonOutput D hdepth hm data hj d c a q ∈
            (base).smoothLocus) := by
  let p₀ := PrimeSpectrum.comap (algebraMap S T) p
  have hp₀ : algebraMap R S π ∈ p₀.asIdeal := by
    change algebraMap S T (algebraMap R S π) ∈ p.asIdeal
    rwa [← IsScalarTower.algebraMap_apply]
  rcases nodalSecant_prime_three_cases D d a c hk (by omega) p hp ha hc with hn | hb | hs
  · exact Or.inr (Or.inl (nodalShallowNegativeBranchOutput_covers
      D hdepth hm data hj d a c hlo hhi p₀ hp₀ hn))
  · exact Or.inr (Or.inr (nodalShallowBranchCommonOutput_covers
      D hdepth hm data hj d c a hlo hhi p₀ hp₀ hb))
  · left
    apply finiteReindexedSmoothSecantOpen_mem d a c p _ hs
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp only [hm, pow_succ, map_mul]
    exact p.asIdeal.mul_mem_left _ hp

end FLT.Mazur.WeierstrassDividedDepth
