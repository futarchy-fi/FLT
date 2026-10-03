/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteOrder
public import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# The actual DVR-adic topology on its fraction field

The maximal-ideal valuation supplies the topology. Its valuation subring
is exactly the image of the DVR, which is therefore an open additive subgroup.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing IsDedekindDomain
open scoped WithZero

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The valued-field structure coming from the actual maximal-ideal adic valuation. -/
@[instance_reducible] def dvrAdicValued : Valued L ℤᵐ⁰ := Valued.mk' ((dvrPrime S).valuation L)

/-- The valuation subring of the maximal-ideal valuation is precisely the DVR image. -/
theorem dvrAdicValued_integers :
    Set.range (algebraMap S L) = (((dvrPrime S).valuation L).valuationSubring : Set L) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact HeightOneSpectrum.valuation_le_one (dvrPrime S) s
  · intro hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv : v = dvrPrime S := HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal inferInstance)
    rw [hv]
    exact hx

/-- Integral elements form an open set in the constructed fraction-field topology. -/
theorem dvrAdicValued_integers_isOpen :
    letI := dvrAdicValued S L
    IsOpen (Set.range (algebraMap S L)) := by
  let := dvrAdicValued S L
  rw [dvrAdicValued_integers]
  exact Valued.isOpen_valuationSubring L

end LocalClassFieldTheory
