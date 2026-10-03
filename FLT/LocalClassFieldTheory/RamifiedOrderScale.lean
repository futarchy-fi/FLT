/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteOrder
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Ramification scales normalized integer order

The adic valuation extension formula gives the actual ramification factor
for an inclusion of DVR fraction fields. This does not assume unramifiedness.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing IsDedekindDomain

variable (R S K L : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]
  [Field K] [Field L] [Algebra K L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [IsScalarTower R K L]
  [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]

/-- The normalized order in the larger fraction field is multiplied by the ramification index. -/
theorem discreteOrder_ramified_scale (x : Kˣ) :
    discreteOrder S L (Units.map (algebraMap K L).toMonoidHom x) =
      discreteOrder R K x ^ (maximalIdeal R).ramificationIdx' (maximalIdeal S) := by
  let : (dvrPrime S).asIdeal.LiesOver (dvrPrime R).asIdeal :=
    inferInstanceAs ((maximalIdeal S).LiesOver (maximalIdeal R))
  have hv := HeightOneSpectrum.valuation_liesOver L (dvrPrime R) (dvrPrime S) (x : K)
  apply Multiplicative.toAdd.injective
  change -WithZero.log ((dvrPrime S).valuation L (algebraMap K L (x : K))) =
    ((maximalIdeal R).ramificationIdx' (maximalIdeal S) : ℤ) *
      -WithZero.log ((dvrPrime R).valuation K (x : K))
  rw [← hv, WithZero.log_pow, nsmul_eq_mul, mul_neg]
  rfl

end LocalClassFieldTheory
