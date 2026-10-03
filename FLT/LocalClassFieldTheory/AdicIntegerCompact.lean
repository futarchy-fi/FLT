/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicSeriesEvaluation
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-!
# Compactness of the actual adic integer ring

Identify the DVR with the valuation integers. Completeness and finiteness
of its residue field then give compactness in the constructed topology.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing Valued.integer
open scoped WithZero

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The original DVR is exactly the integer ring of its constructed valuation. -/
def dvrValuedIntegerEquiv :
    letI := dvrAdicValued S L
    S ≃+* Valued.integer L := by
  let := dvrAdicValued S L
  let f := (algebraMap S L).codRestrict (Valued.integer L)
    (IsDedekindDomain.HeightOneSpectrum.valuation_le_one (dvrPrime S))
  apply RingEquiv.ofBijective f
  constructor
  · intro x y h
    exact IsFractionRing.injective S L (congrArg Subtype.val h)
  · intro x
    obtain ⟨s, hs⟩ := (Set.ext_iff.mp (dvrAdicValued_integers S L) x.val).mpr x.property
    exact ⟨s, Subtype.ext hs⟩

/-- Complete DVRs with finite residue field have compact valuation integers. -/
theorem dvrValuedInteger_compactSpace [IsAdicComplete (maximalIdeal S) S]
    [Finite (ResidueField S)] :
    letI := dvrAdicValued S L
    CompactSpace (Valued.integer L) := by
  let := dvrAdicValued S L
  let : CompleteSpace L := adicFractionFieldComplete S L
  let : CompleteSpace (Valued.integer L) := (Valued.isClosed_integer L).completeSpace_coe
  let : IsDiscreteValuationRing (Valued.integer L) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (dvrValuedIntegerEquiv S L)
  let : Finite (ResidueField (Valued.integer L)) :=
    Finite.of_equiv _ (ResidueField.mapEquiv (dvrValuedIntegerEquiv S L)).toEquiv
  let : (Valued.v : Valuation L ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (v := (dvrPrime S).valuation L)
      (by norm_num : (1 : NNReal) < 2)
  exact compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- Compactness transferred to the topological integer copy used by local series. -/
instance instAdicIntegerCompactSpace [IsAdicComplete (maximalIdeal S) S]
    [Finite (ResidueField S)] : CompactSpace (AdicInteger S L) := by
  let := dvrAdicValued S L
  let := dvrValuedInteger_compactSpace S L
  let e := (dvrValuedIntegerEquiv S L).symm.trans (adicIntegerEquiv S L).symm
  have he : Continuous e := by
    apply (adicIntegerToField_isUniformInducing S L).isInducing.continuous_iff.mpr
    have h : adicIntegerToField S L ∘ e = Subtype.val := by
      funext x
      exact congrArg Subtype.val ((dvrValuedIntegerEquiv S L).apply_symm_apply x)
    rw [h]
    exact continuous_subtype_val
  exact ⟨by simpa only [Set.image_univ, Set.range_eq_univ.mpr e.surjective]
    using isCompact_univ.image he⟩

end LocalClassFieldTheory
