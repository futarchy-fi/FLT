/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.HasGoingUp

/-! # Krull dimension is unchanged by an injective integral extension -/

@[expose] public noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Incomparability bounds the dimension of an integral algebra by that of its base. -/
theorem ringKrullDim_le_of_integral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    (fun _ _ h ↦ Ideal.IsIntegral.under_lt_under h)

/-- Lying over and going up lift every finite chain, while incomparability reflects it. -/
theorem ringKrullDim_eq_of_integral_injective [Algebra.IsIntegral R S]
    (h : Function.Injective (algebraMap R S)) : ringKrullDim S = ringKrullDim R := by
  refine le_antisymm ringKrullDim_le_of_integral ?_
  change Order.krullDim (PrimeSpectrum R) ≤ _
  apply iSup_le
  intro l
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr h
  obtain ⟨P, hP⟩ := Algebra.IsIntegral.comap_surjective R S l.head
  have : P.asIdeal.LiesOver l.head.asIdeal :=
    (Ideal.liesOver_iff _ _).mpr (congrArg PrimeSpectrum.asIdeal hP).symm
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  simpa only [hL, ringKrullDim] using Order.LTSeries.length_le_krullDim L

end
