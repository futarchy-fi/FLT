/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleDimLe
public import Mathlib.RingTheory.Ideal.HasGoingUp
/-!
# Dimension descent through going up

Surjective contraction and going up lift every finite prime chain without
changing its length. Thus the base has no larger Krull dimension.
-/

@[expose] public section
open Order
namespace FLT.Mazur.IntegralDimension
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
/-- Lift prime chains to bound the dimension of the base. -/
theorem le [Algebra.HasGoingUp R S]
    (hs : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    ringKrullDim R ≤ ringKrullDim S := by
  rw [ringKrullDim, krullDim]
  apply iSup_le
  intro l
  obtain ⟨P, hP⟩ := hs l.head
  have : P.asIdeal.LiesOver l.head.asIdeal := ⟨by
    exact (congrArg PrimeSpectrum.asIdeal hP).symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  rw [← hL]
  exact L.length_le_krullDim
end FLT.Mazur.IntegralDimension
