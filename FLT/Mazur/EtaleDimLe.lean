/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Dimension bounds for étale algebras

A quasi-finite algebra has Artinian, hence zero-dimensional, fibers. Incomparability
then says that comparable prime ideals with the same contraction are equal. Thus
contraction preserves strict prime chains, and the algebra has Krull dimension at
most that of the base ring.

Specializing to an étale algebra over a polynomial ring in one variable over a field
gives the upper bound needed by FC12b of `docs/FCURVE_CONTRACTS.md`. The algebra need
not be a domain or nontrivial; the zero ring has Krull dimension negative infinity.
-/

@[expose] public section

namespace Algebra.QuasiFinite

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [QuasiFinite R S]

/-- Every fiber of a quasi-finite algebra has Krull dimension at most zero. -/
theorem ringKrullDim_fiber_le_zero (p : Ideal R) [p.IsPrime] :
    ringKrullDim (p.Fiber S) ≤ 0 := by
  exact (Ring.krullDimLE_iff (n := 0)).mp inferInstance

/-- Contraction of primes along a quasi-finite algebra preserves strict inclusion.
Incomparability within its zero-dimensional fibers supplies strictness. -/
theorem strictMono_comap : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro p q hpq
  refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
  intro h
  have hpq' : p.asIdeal = q.asIdeal := eq_of_le_of_under_eq p.asIdeal q.asIdeal hpq.le
    (congrArg (fun r : PrimeSpectrum R ↦ r.asIdeal) h)
  exact hpq.ne (PrimeSpectrum.ext hpq')

/-- A quasi-finite algebra cannot have greater Krull dimension than its base. -/
theorem ringKrullDim_le : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono _ (strictMono_comap R S)

/-- A finite upper bound on Krull dimension passes to quasi-finite algebras. -/
theorem krullDimLE (n : ℕ) [Ring.KrullDimLE n R] : Ring.KrullDimLE n S := by
  apply Ring.krullDimLE_iff.mpr
  exact (ringKrullDim_le R S).trans (Ring.krullDimLE_iff.mp inferInstance)

end Algebra.QuasiFinite

namespace FLT.Mazur.FCurve

variable (K S : Type*) [Field K] [CommRing S] [Algebra (Polynomial K) S]

/-- A quasi-finite algebra over the affine line has Krull dimension at most one. -/
theorem ringKrullDim_le_one_of_quasiFinite_polynomial
    [Algebra.QuasiFinite (Polynomial K) S] : ringKrullDim S ≤ 1 := by
  have hbase : ringKrullDim (Polynomial K) ≤ 1 := by
    exact (Ring.krullDimLE_iff (n := 1)).mp inferInstance
  exact (Algebra.QuasiFinite.ringKrullDim_le (Polynomial K) S).trans hbase

/-- An étale algebra over `K[t]` has Krull dimension at most one. -/
theorem ringKrullDim_le_one_of_etale_polynomial
    [Algebra.Etale (Polynomial K) S] : ringKrullDim S ≤ 1 :=
  ringKrullDim_le_one_of_quasiFinite_polynomial K S

/-- The dimension bound for an étale `K[t]`-algebra, in typeclass form. -/
theorem krullDimLE_one_of_etale_polynomial
    [Algebra.Etale (Polynomial K) S] : Ring.KrullDimLE 1 S := by
  exact Ring.krullDimLE_iff.mpr (ringKrullDim_le_one_of_etale_polynomial K S)

end FLT.Mazur.FCurve
