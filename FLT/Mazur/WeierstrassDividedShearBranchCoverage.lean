/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearBranchSource
public import FLT.Mazur.WeierstrassDividedNodalSecondNormalization

/-!
# The normalized branch has the original special-fiber domain

The genuine branch principal opens have identical special-fiber points.
The chosen finite normalization supplies the needed vanishing of the shear;
there is no extra branch coverage assumption.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth IsLocalRing
attribute [local irreducible] rootShearCurve
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "V" => rootShearCurve W r
local notation "a'" => branchShearInput W s b3 b4 b6 r a
local notation "c'" => branchShearInput W s b3 b4 b6 r c
local notation "old" => dividedTangentDenominator W s b3 b4 b6 a c *
  dividedTangentBranchFactor W s b3 b4 b6 a
local notation "new" => dividedTangentDenominator V s b3 (b4 - r * b3) b6 a' c' *
  dividedTangentBranchFactor V s b3 (b4 - r * b3) b6 a'

/-- At a prime containing the shear, the two actual branch domains coincide. -/
theorem branchShearInput_basicOpen_iff (p : PrimeSpectrum S)
    (hr : algebraMap R S r ∈ p.asIdeal) :
    p ∈ PrimeSpectrum.basicOpen new ↔ p ∈ PrimeSpectrum.basicOpen old := by
  let f := Ideal.Quotient.mk p.asIdeal
  have hs := branchShearInput_specialization W s b3 b4 b6 r a c f
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have he : f new = f old := by rw [map_mul, map_mul, hs.1, hs.2]
  change new ∉ p.asIdeal ↔ old ∉ p.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  exact not_congr (Iff.of_eq (congrArg (· = 0) he))

variable [IsLocalRing R] {π : R} {m : ℕ} (D : SplitNodeDepth W π m) (k : ℕ)

/-- The constructed finite normalization vanishes at every original special-fiber prime. -/
theorem nodalSecondShear_mem_prime (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) :
    algebraMap R S (nodalSecondShear D k) ∈ p.asIdeal := by
  have h := nodalSecondShear_mem D k
  rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at h
  obtain ⟨z, hz⟩ := h
  rw [hz, map_mul]
  exact p.asIdeal.mul_mem_right _ hp

/-- The finite normalized branch and original branch cover exactly the same special fiber. -/
theorem nodalSecondShear_branch_basicOpen_iff (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) :
    let t := nodalSecondShear D k
    let U := rootShearCurve W t
    let a₁ := branchShearInput W s b3 b4 b6 t a
    let c₁ := branchShearInput W s b3 b4 b6 t c
    p ∈ PrimeSpectrum.basicOpen
        (dividedTangentDenominator U s b3 (b4 - t * b3) b6 a₁ c₁ *
          dividedTangentBranchFactor U s b3 (b4 - t * b3) b6 a₁) ↔
      p ∈ PrimeSpectrum.basicOpen old :=
  branchShearInput_basicOpen_iff W s b3 b4 b6 (nodalSecondShear D k) a c p
    (nodalSecondShear_mem_prime W D k p hp)

end FLT.Mazur.WeierstrassDilatation
