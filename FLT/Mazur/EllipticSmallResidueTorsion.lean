/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFinitePointBound
public import FLT.Mazur.EllipticPrimeToResidueSpecialization

/-!
# Large prime torsion cannot reduce smoothly over a small residue field

The elementary q² + 1 point bound kills the specialized prime torsion.
Prime-to-residue injectivity then kills the original smooth point, including
at residue characteristic two and without an unramifiedness hypothesis.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]

/-- Prime-to-residue torsion in E₀ is zero once the prime exceeds the coordinate count. -/
theorem smooth_prime_torsion_eq_zero_of_residue_card_bound
    (q p : ℕ) [CharP (ResidueField A) q] (hp : p.Prime) (hqp : ¬ q ∣ p)
    (hcard : Nat.card (ResidueField A) ^ 2 + 1 < p)
    (P : ellipticE0 A W) (hP : p • P = 0) : P = 0 := by
  classical
  apply smoothReductionHom_torsion_eq_zero_of_not_dvd A W q p hqp P hP
  let T := Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective
  apply T.injective
  rw [map_zero]
  let Q := T (smoothReductionHom A W P)
  change Q = 0
  have hn : p • Q = 0 := by
    simp only [Q, ← map_nsmul, hP, map_zero]
  let _ := finite_affinePoints_of_finite (W.map (residue A))
  have hd : addOrderOf Q ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | he
  · have h := addOrderOf_nsmul_eq_zero Q
    simpa only [h1, one_nsmul] using h
  · have hl := Nat.le_of_dvd
      (Nat.card_pos (α := (W.map (residue A)).toAffine.Point)) (addOrderOf_dvd_natCard Q)
    have hb := card_affinePoints_le_square_add_one (W.map (residue A))
    omega

/-- The exact original nonzero point lies outside E₀ under the small-residue bound. -/
theorem not_smoothReduction_prime_torsion_of_residue_card_bound
    (q p : ℕ) [CharP (ResidueField A) q] (hp : p.Prime) (hqp : ¬ q ∣ p)
    (hcard : Nat.card (ResidueField A) ^ 2 + 1 < p)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hne : P ≠ 0)
    (hP : p • P = 0) : ¬ SmoothReduction A W P := by
  intro hs
  let Q : ellipticE0 A W := ⟨P, hs⟩
  have hz := smooth_prime_torsion_eq_zero_of_residue_card_bound A W q p hp hqp hcard Q
    (Subtype.ext hP)
  exact hne (congrArg (ellipticE0 A W).subtype hz)

end FLT.Mazur
