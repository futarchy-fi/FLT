/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearBranchOverlap
public import FLT.Mazur.WeierstrassDividedShearBranchCoverage

/-!
# The common tangent domain covers the entire original branch special fiber

Inverting the original tangent denominator in addition to the normalized
branch factors loses no original strict-branch point where the shear
vanishes. Finite nodal normalization supplies this vanishing itself.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "V" => rootShearCurve W r
local notation "a'" => branchShearInput W s b3 b4 b6 r a
local notation "c'" => branchShearInput W s b3 b4 b6 r c
local notation "D" => dividedTangentDenominator W s b3 b4 b6 a c
local notation "C" => dividedTangentBranchFactor W s b3 b4 b6 a
local notation "N" => dividedTangentDenominator V s b3 (b4 - r * b3) b6 a' c' *
  dividedTangentBranchFactor V s b3 (b4 - r * b3) b6 a'
local notation "O" => DividedShearBranchOverlap W s b3 b4 b6 r a c

/-- The constructed common source covers every branch prime at which the shear vanishes. -/
theorem dividedShearBranchOverlap_covers (p : PrimeSpectrum S)
    (hr : algebraMap R S r ∈ p.asIdeal) (hb : p ∈ PrimeSpectrum.basicOpen (D * C)) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p := by
  have hn := (branchShearInput_basicOpen_iff W s b3 b4 b6 r a c p hr).mpr hb
  have hd : D ∉ p.asIdeal := by
    intro hd
    exact hb (p.asIdeal.mul_mem_right _ hd)
  have hdn : p ∈ PrimeSpectrum.basicOpen (D * N) := by
    intro hdn
    exact (p.isPrime.mem_or_mem hdn).elim hd hn
  exact (PrimeSpectrum.localization_away_comap_range O (D * N)).ge hdn

variable [IsLocalRing R] {π : R} {m : ℕ} (depth : SplitNodeDepth W π m) (k : ℕ)

/-- Constructed nodal normalization retains every original strict-branch special-fiber point. -/
theorem nodalShearBranchOverlap_covers (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hb : p ∈ PrimeSpectrum.basicOpen (D * C)) :
    let t := nodalSecondShear depth k
    let A := DividedShearBranchOverlap W s b3 b4 b6 t a c
    ∃ q : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap S A) q = p ∧
      algebraMap R A π ∈ q.asIdeal := by
  let t := nodalSecondShear depth k
  let A := DividedShearBranchOverlap W s b3 b4 b6 t a c
  obtain ⟨q, hq⟩ := dividedShearBranchOverlap_covers W s b3 b4 b6 t a c p
    (nodalSecondShear_mem_prime W depth k p hp) hb
  refine ⟨q, hq, ?_⟩
  have h : algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S A) q).asIdeal := hq ▸ hp
  change algebraMap S A (algebraMap R S π) ∈ q.asIdeal at h
  change algebraMap R A π ∈ q.asIdeal
  rw [IsScalarTower.algebraMap_apply R S A]
  exact h

end FLT.Mazur.WeierstrassDilatation
