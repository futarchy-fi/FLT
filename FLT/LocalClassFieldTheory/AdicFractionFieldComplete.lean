/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicIntegerTopology
public import FLT.LocalClassFieldTheory.LocalExpRadius
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Completeness of the actual adic fraction field

An algebraically complete DVR has complete image in its fraction field.
This image is a neighborhood of zero; every Cauchy filter has a tail in
a translate of it and hence converges. The exponential convergence theorem
therefore needs no additional completeness premise.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Filter IsLocalRing
open scoped Topology WithZero

/-- A complete neighborhood of zero makes a uniform additive group complete. -/
theorem completeSpace_of_complete_zero_neighborhood
    {A : Type*} [AddCommGroup A] [UniformSpace A] [IsUniformAddGroup A]
    {U : Set A} (hU : IsComplete U) (h0 : U ∈ 𝓝 (0 : A)) : CompleteSpace A where
  complete {f} hf := by
    have : f.NeBot := hf.1
    have ht := (IsUniformAddGroup.cauchy_iff_tendsto_swapped f).mp hf |>.2
    obtain ⟨x, hx⟩ : ∃ x, ∀ᶠ y in f, y - x ∈ U :=
      (ht.eventually h0).curry.exists
    have hc : IsComplete ((fun y => y + x) '' U) :=
      (isUniformEmbedding_translate_add x).isUniformInducing.isComplete_iff.mpr hU
    obtain ⟨l, _, hl⟩ := hc f hf (by
      apply le_principal_iff.mpr
      filter_upwards [hx] with y hy
      exact ⟨y - x, hy, sub_add_cancel y x⟩)
    exact ⟨l, hl⟩

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]
  [IsAdicComplete (maximalIdeal S) S]

/-- Algebraic adic completeness makes the DVR image a complete subset. -/
theorem dvrAdicValued_integers_isComplete :
    letI := dvrAdicValued S L
    IsComplete (Set.range (algebraMap S L)) := by
  let := dvrAdicValued S L
  let := dvrIntegerUniformity S L
  let : IsUniformAddGroup S := IsUniformAddGroup.comap (algebraMap S L)
  let : CompleteSpace S := (dvrIntegerUniformity_isAdic S L).isPrecomplete_iff.mp
    (inferInstance : IsPrecomplete (maximalIdeal S) S)
  have hi : IsUniformInducing (algebraMap S L) := ⟨rfl⟩
  exact hi.isComplete_range

/-- The fraction field of an adically complete DVR is complete for its actual
maximal-ideal valuation, without an extra topological completeness assumption. -/
theorem adicFractionFieldComplete :
    letI := dvrAdicValued S L
    CompleteSpace L := by
  let := dvrAdicValued S L
  exact completeSpace_of_complete_zero_neighborhood
    (dvrAdicValued_integers_isComplete S L)
    ((dvrAdicValued_integers_isOpen S L).mem_nhds ⟨0, map_zero _⟩)

/-- Exponential summability derived from the program's complete DVR assumptions. -/
theorem adicLocalExp_summable [CharZero L] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    letI := dvrAdicValued S L
    Summable (fun n : ℕ => x ^ n / (n.factorial : L)) :=
  localExp_summable S L p x hx (adicFractionFieldComplete S L)

end LocalClassFieldTheory
