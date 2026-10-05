/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCuspidalGroup
public import FLT.Mazur.EllipticPrimeToResidueSpecialization
public import FLT.Mazur.EllipticPrimeTorsionComponents

/-!
# Excluding additive reduction with large prime torsion

A cuspidal special fiber has no prime-to-residue torsion on its smooth
locus. Injectivity of specialization and the actual component bound then
exclude additive reduction on a minimal equation carrying nonzero p-torsion,
when p>4 and p differs from the residue characteristic.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]

/-- Prime-to-residue torsion in E₀ is zero for a cuspidal special fiber. -/
theorem ellipticE0_torsion_eq_zero_of_additive
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : W.c₄ ∈ maximalIdeal A)
    (q n : ℕ) [CharP (ResidueField A) q] (hn : ¬ q ∣ n)
    (P : ellipticE0 A W) (hP : n • P = 0) : P = 0 := by
  classical
  apply smoothReductionHom_torsion_eq_zero_of_not_dvd A W q n hn P hP
  apply (Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective).injective
  rw [map_zero]
  apply cuspidalPoint_torsion_eq_zero (W.map (residue A))
    (by rw [map_Δ]; exact (residue_eq_zero_iff _).mpr hΔ)
    (by rw [map_c₄]; exact (residue_eq_zero_iff _).mpr hc) q n hn
  rw [← map_nsmul, ← map_nsmul, hP, map_zero, map_zero]

variable [IsDiscreteValuationRing A] [(W.map (algebraMap A K)).IsElliptic]
  [IsMinimal A (W.map (algebraMap A K))]

/-- On a minimal additive equation, prime-to-residue p-torsion is zero for p>4. -/
theorem prime_torsion_eq_zero_of_minimalAdditive
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : W.c₄ ∈ maximalIdeal A)
    (q p : ℕ) [CharP (ResidueField A) q] (hp : p.Prime) (hp4 : 4 < p)
    (hqp : ¬ q ∣ p) (P : (W.map (algebraMap A K)).toProjective.Point)
    (hP : p • P = 0) : P = 0 := by
  let Q : ellipticE0 A W :=
    ⟨P, smoothReduction_prime_torsion_minimalAdditive A W hΔ hc hp hp4 P hP⟩
  have hQ : p • Q = 0 := Subtype.ext hP
  exact congrArg (fun R : ellipticE0 A W => R.val)
    (ellipticE0_torsion_eq_zero_of_additive A W hΔ hc q p hqp Q hQ)

/-- A nonzero large prime torsion point forces unit c₄ at every bad prime away from p. -/
theorem isUnit_c₄_of_prime_torsion
    (hΔ : W.Δ ∈ maximalIdeal A) (q p : ℕ) [CharP (ResidueField A) q]
    (hp : p.Prime) (hp4 : 4 < p) (hqp : ¬ q ∣ p)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hne : P ≠ 0)
    (hP : p • P = 0) : IsUnit W.c₄ := by
  by_contra hc
  exact hne (prime_torsion_eq_zero_of_minimalAdditive A W hΔ
    (by rwa [mem_maximalIdeal, mem_nonunits_iff]) q p hp hp4 hqp P hP)

end FLT.Mazur
