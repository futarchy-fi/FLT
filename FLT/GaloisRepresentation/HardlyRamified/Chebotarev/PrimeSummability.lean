/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AINTLIB.CebotarevDensity.NumberFieldEulerProduct

/-!
# Summability of prime-ideal norm powers

This proves leaf Z2 of `docs/CHEBOTAREV_PLAN.md`. The statement spells out the
plan's proposed `Prime K` and `norm v` wrappers as `HeightOneSpectrum (𝓞 K)` and
`v.asIdeal.absNorm`. Restriction to any set of primes follows from `Summable.subtype`.
-/

public section

open NumberField IsDedekindDomain

namespace Chebotarev

/-- The prime-ideal norm series converges for every real exponent greater than one. -/
theorem summable_primeNorm (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.asIdeal.absNorm : ℝ) ^ (-s)) := by
  let ι : HeightOneSpectrum (𝓞 K) → NonzeroIdeal K := fun v ↦ ⟨v.asIdeal, v.ne_bot⟩
  have hι : Function.Injective ι := fun _ _ h ↦
    HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h)
  have hsum := (hasSum_nonzeroIdeal_absNorm_cpow K (s := (s : ℂ)) hs).summable
  apply Complex.summable_ofReal.mp
  simpa only [Function.comp_def, ι, Complex.ofReal_cpow (Nat.cast_nonneg _) (-s),
    Complex.ofReal_natCast, Complex.ofReal_neg] using hsum.comp_injective hι

end Chebotarev
