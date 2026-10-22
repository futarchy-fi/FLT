/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordPrimeCoverage
public import FLT.Mazur.WeierstrassDividedMiddleTangentCoverage

/-!
# Complete middle-depth coverage by tangent and reciprocal chord outputs

At exact middle depth the chord numerator is a unit in every closed-fiber
residue field. Thus every input reaches either the existing tangent output
or the new genuine infinity output. No abscissa or vertical puncture is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (node : SplitNodeDepth W π depth) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "num" => dividedTangentNumerator W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "den" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c

include node

/-- Every middle-depth input has a nonzero divided chord numerator in its residue field. -/
theorem middleChordNumerator_not_mem (hk : 0 < k) (hm : 2 * k = depth)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal) : num ∉ p.asIdeal := by
  let K := p.asIdeal.ResidueField
  let e : S →ₐ[R] K := IsScalarTower.toAlgHom R S K
  have hπ : algebraMap R K π = 0 := by
    rw [IsScalarTower.algebraMap_apply R S K]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hp
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
    rw [node.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, rfl⟩ := hb
    rw [map_mul, hπ, zero_mul]
  have hs : algebraMap R K (π ^ k) = 0 := by
    rw [map_pow, hπ, zero_pow (by omega)]
  have hlin := divided_linear_deep_mem node d (by omega : k ≤ depth + 1)
  have h3 := van d.b3 (Ideal.pow_le_self (by omega) hlin.1)
  have h4 := van d.b4 (Ideal.pow_le_self (by omega) hlin.2)
  have h2 := van W.a₂ node.a₂_mem
  have h6 := (unequalDepthMiddle_constant_unit node d hm).map (algebraMap R K)
  have ha := node.a₁_unit.map (algebraMap R K)
  have he := equation_map W (π ^ k) d.b3 d.b4 d.b6 (e.comp a)
  simp only [hs, h2, h3, h4, zero_mul, zero_add, add_zero] at he
  have hv : IsUnit ((e.comp a) (y W (π ^ k) d.b3 d.b4 d.b6)) := by
    apply isUnit_of_mul_isUnit_left (y :=
      (e.comp a) (y W (π ^ k) d.b3 d.b4 d.b6) +
        algebraMap R K W.a₁ * (e.comp a) (x W (π ^ k) d.b3 d.b4 d.b6))
    convert h6 using 1
    linear_combination he
  have hs' : algebraMap R K π ^ k = 0 := by simpa only [map_pow] using hs
  have hn : e num = -(algebraMap R K W.a₁ *
      (e.comp a) (y W (π ^ k) d.b3 d.b4 d.b6)) := by
    simp only [dividedTangentNumerator, map_add, map_sub, map_mul, map_pow,
      AlgHom.commutes, hs', h2, h4, zero_mul, zero_add, zero_sub, AlgHom.comp_apply]
  intro h
  apply (ha.mul hv).neg.ne_zero
  rw [← hn]
  exact Ideal.algebraMap_residueField_eq_zero.mpr h

/-- The previously missing zero-denominator middle pairs have an actual smooth infinity output. -/
theorem suppliedReciprocalChordDomain_middle_mem (hk : 0 < k) (hm : 2 * k = depth)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal) (hd : den ∈ p.asIdeal) :
    p ∈ suppliedReciprocalChordDomain d a c := by
  exact suppliedReciprocalChordDomain_mem d a c p hd
    (middleChordNumerator_not_mem node d a c hk hm p hp)

/-- These two constructed output domains exhaust all exact-middle closed-fiber inputs. -/
theorem middleTangentReciprocalChord_cover (hk : 0 < k) (hm : 2 * k = depth)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal) :
    p ∈ suppliedSmoothTangentDomain d a c ∨ p ∈ suppliedReciprocalChordDomain d a c := by
  by_cases hd : den ∈ p.asIdeal
  · exact Or.inr (suppliedReciprocalChordDomain_middle_mem node d a c hk hm p hp hd)
  · exact Or.inl (suppliedSmoothTangentDomain_middle_mem node d a c hk hm p hp hd)

end FLT.Mazur.WeierstrassDividedDepth
