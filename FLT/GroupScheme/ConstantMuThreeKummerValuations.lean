/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantMuThreeKummerCocycle
public import FLT.Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Valuations of the actual extension's Kummer parameter

The original finite-flat middle model is killed by three, so its full point
field is unramified away from two and three. A cube root in that field forces
the rational parameter's valuation to be divisible by three at those primes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open NumberField IsDedekindDomain

namespace ThreeAdicPlan

/-- A rational number with a cube root in a number field unramified at `p`
has `p`-adic valuation divisible by three. -/
theorem three_dvd_rational_valuation_of_unramified_cube
    (L : Type) [Field L] [NumberField L] (a : ℚ) (ha : a ≠ 0)
    (b : L) (hb : b ^ 3 = algebraMap ℚ L a) (p : ℕ) (hp : p.Prime)
    (hunr : Algebra.IsUnramifiedIn (𝓞 L) hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) :
    (3 : ℤ) ∣ padicValRat p a := by
  let primeP : Fact p.Prime := ⟨hp⟩
  let v := hp.toHeightOneSpectrumRingOfIntegersRat
  obtain ⟨P, hP, hPv⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain v.asIdeal (S := 𝓞 L) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 L))]
      exact bot_le)
  let primeIdeal : P.IsPrime := hP
  let liesOver : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
    exact hunr.ramificationIdx_eq_one liesOver
  have hv := v.valuation_liesOver L w a
  rw [he, pow_one, ← hb, map_pow] at hv
  rw [Rat.HeightOneSpectrum.valuation_apply_eq_padicValuation,
    primesEquiv_ratPrime p hp] at hv
  have hlog := congrArg WithZero.log hv
  change WithZero.log (if a = 0 then 0 else WithZero.exp (-padicValRat p a)) =
    WithZero.log (w.valuation L b ^ 3) at hlog
  simp only [ha, ↓reduceIte, WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  refine ⟨-WithZero.log (w.valuation L b), ?_⟩
  linarith

namespace FiniteFlatExtension

variable {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree)

include E in
/-- The full field of the actual extension is unramified away from two and three. -/
theorem constantThree_muThree_pointField_unramified (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Algebra.IsUnramifiedIn (𝓞 X.points.pointField)
      hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
  X.points.pointField_isUnramifiedIn
    (X.unramifiedOutside_of_killedBy_three E.constantThree_muThree_nsmul)
    p hp (by simp [hp2, hp3])

include E in
/-- Every nonzero Kummer parameter produced in the actual point field has
valuation divisible by three away from two and three. -/
theorem actual_cubic_kummer_parameter_away_valuations (a : ℚ) (ha : a ≠ 0)
    (b : X.points.pointField) (hb : b ^ 3 = algebraMap ℚ X.points.pointField a)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (3 : ℤ) ∣ padicValRat p a :=
  three_dvd_rational_valuation_of_unramified_cube X.points.pointField a ha b hb p hp
    (E.constantThree_muThree_pointField_unramified p hp hp2 hp3)

end FiniteFlatExtension
end ThreeAdicPlan
