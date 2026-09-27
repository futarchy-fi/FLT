/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prime fibers in a Galois extension

Leaf B2 of `docs/CHEBOTAREV_PLAN.md`: the norm-power sum over a prime fiber,
its contribution at a split prime, and the lower bound on nonsplit residue degrees.
The norm-power formula in fact holds at ramified primes too; the requested
unramified version is retained as a wrapper. Norms are `Ideal.absNorm`.
-/

@[expose] public section

open NumberField

namespace GaloisRepresentation.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Every prime in a Galois fiber has the same absolute norm. -/
theorem absNorm_eq_pow_inertiaDegIn (v : Prime K)
    (w : Ideal.primesOver v.asIdeal (𝓞 L)) :
    w.1.absNorm = v.asIdeal.absNorm ^ v.asIdeal.inertiaDegIn (𝓞 L) := by
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1 Gal(L/K)]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1).symm

/-- The sum of norm powers over a Galois prime fiber. -/
theorem sum_norm_powers_over (v : Prime K) (s : ℝ) :
    ∑ w : Ideal.primesOver v.asIdeal (𝓞 L), (w.1.absNorm : ℝ) ^ (-s) =
      (Nat.card (Ideal.primesOver v.asIdeal (𝓞 L)) : ℝ) *
        (v.asIdeal.absNorm : ℝ) ^ (-(s * v.asIdeal.inertiaDegIn (𝓞 L))) := by
  have h (w : Ideal.primesOver v.asIdeal (𝓞 L)) :
      (w.1.absNorm : ℝ) ^ (-s) =
        (v.asIdeal.absNorm : ℝ) ^ (-(s * v.asIdeal.inertiaDegIn (𝓞 L))) := by
    rw [absNorm_eq_pow_inertiaDegIn K L v w, Nat.cast_pow,
      ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  simp_rw [h]
  simp [Nat.card_eq_fintype_card]

/-- The norm-power formula at an unramified prime, in the form of leaf B2. -/
@[nolint unusedArguments]
theorem sum_norm_powers_over_unramified (v : Prime K) (_hu : Unram K L v) (s : ℝ) :
    ∑ w : Ideal.primesOver v.asIdeal (𝓞 L), (w.1.absNorm : ℝ) ^ (-s) =
      (Nat.card (Ideal.primesOver v.asIdeal (𝓞 L)) : ℝ) *
        (v.asIdeal.absNorm : ℝ) ^ (-(s * v.asIdeal.inertiaDegIn (𝓞 L))) :=
  sum_norm_powers_over K L v s

/-- At an unramified prime, the fiber size times the residue degree is `[L : K]`. -/
theorem card_primesOver_mul_inertiaDegIn (v : Prime K) (hu : Unram K L v) :
    Nat.card (Ideal.primesOver v.asIdeal (𝓞 L)) * v.asIdeal.inertiaDegIn (𝓞 L) =
      Module.finrank K L := by
  let w := primeAbove K L v
  let : w.asIdeal.LiesOver v.asIdeal := ⟨(primeAbove_under K L v).symm⟩
  let : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := hu _ inferInstance inferInstance
  have he : v.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v.asIdeal (𝓞 L) Gal(L/K)
  rw [he, one_mul, IsGalois.card_aut_eq_finrank] at h
  exact h

/-- A trivial Frobenius gives residue degree one throughout its unramified fiber. -/
theorem inertiaDegIn_eq_one_of_frob_eq_one (v : Prime K) (hu : Unram K L v)
    (hf : frob K L v = 1) : v.asIdeal.inertiaDegIn (𝓞 L) = 1 := by
  let : (primeAbove K L v).asIdeal.LiesOver v.asIdeal :=
    ⟨(primeAbove_under K L v).symm⟩
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal (primeAbove K L v).asIdeal Gal(L/K),
    ← orderOf_frob_eq_inertiaDeg K L v _ (primeAbove_under K L v) hu, hf, orderOf_one]

/-- The fiber of an unramified split prime contributes `[L : K]` equal terms. -/
theorem sum_norm_powers_over_split (v : Prime K) (hu : Unram K L v)
    (hf : frob K L v = 1) (s : ℝ) :
    ∑ w : Ideal.primesOver v.asIdeal (𝓞 L), (w.1.absNorm : ℝ) ^ (-s) =
      (Module.finrank K L : ℝ) * (v.asIdeal.absNorm : ℝ) ^ (-s) := by
  have hd := inertiaDegIn_eq_one_of_frob_eq_one K L v hu hf
  have hc := card_primesOver_mul_inertiaDegIn K L v hu
  rw [hd, mul_one] at hc
  rw [sum_norm_powers_over K L v s, hd, hc, Nat.cast_one, mul_one]

/-- A nontrivial Frobenius at an unramified prime forces residue degree at least two. -/
theorem two_le_inertiaDegIn_of_frob_ne_one (v : Prime K) (hu : Unram K L v)
    (hf : frob K L v ≠ 1) : 2 ≤ v.asIdeal.inertiaDegIn (𝓞 L) := by
  let : (primeAbove K L v).asIdeal.LiesOver v.asIdeal :=
    ⟨(primeAbove_under K L v).symm⟩
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal (primeAbove K L v).asIdeal Gal(L/K),
    ← orderOf_frob_eq_inertiaDeg K L v _ (primeAbove_under K L v) hu]
  have hpos := orderOf_pos (frob K L v)
  have hne : orderOf (frob K L v) ≠ 1 := fun h ↦ hf (orderOf_eq_one_iff.mp h)
  omega

end GaloisRepresentation.Chebotarev
