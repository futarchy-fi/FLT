/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.LogDensity
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.NonsplitBound

/-!
# Density of completely split primes

Leaf B4 of `docs/CHEBOTAREV_PLAN.md`: in a finite Galois extension `L/K`,
the completely split primes have logarithmic density `1 / [L : K]`.
The bounded error from B3 vanishes after logarithmic normalization, and Z4
gives the normalized prime sum of `L`.

The two existing `LogDensity` definitions are definitionally equal; this file
uses `GaloisRepresentation.Chebotarev.LogDensity` and introduces no new definition.
-/

public section

open Filter NumberField
open scoped Topology

namespace GaloisRepresentation.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Completely split primes have logarithmic density equal to the reciprocal
of the degree of the Galois extension. -/
theorem logDensity_split :
    LogDensity (Split K L) (1 / (Module.finrank K L : ℝ)) := by
  have huniv : LogDensity (Set.univ : Set (Prime L)) 1 :=
    _root_.Chebotarev.logDensity_univ
  have herror := tendsto_div_ell_of_isBigO (primeSum_sub_splitPrimeSum_bounded K L)
  have hmain : Tendsto (fun s ↦ (Module.finrank K L : ℝ) * ps (Split K L) s / ell s)
      (𝓝[>] 1) (𝓝 1) := by
    simpa only [sub_div, sub_sub_cancel, sub_zero] using huniv.sub herror
  have hn : (Module.finrank K L : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := K) (M := L)))
  simpa only [LogDensity, mul_div_assoc, mul_div_cancel_left₀ _ hn] using
    hmain.div_const (Module.finrank K L : ℝ)

end GaloisRepresentation.Chebotarev
