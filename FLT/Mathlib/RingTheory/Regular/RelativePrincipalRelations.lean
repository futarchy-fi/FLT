/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.CommonDenominatorRelations
public import FLT.Mathlib.RingTheory.Localization.PrincipalIdealComparison

/-! # Spread a finite local kernel with a regular specified reduction -/

@[expose] public noncomputable section

namespace Ideal

variable {R U : Type*} [CommRing R] [CommRing U]

/-- Clear local relation denominators and spread generation of the entire finite
kernel. The specified reduction remains regular at the original point. -/
theorem exists_principal_relations_of_regular_reduction
    (P : Ideal R) [P.IsPrime] (I : Ideal R) (hI : I.FG)
    (rs : List (Localization.AtPrime P))
    (hgen : Ideal.ofList rs = I.map (algebraMap R _))
    (φ : Localization.AtPrime P →+* U)
    (hreg : RingTheory.Sequence.IsRegular U (rs.map φ)) :
    ∃ (a : R) (qs : List R), a ∉ P ∧ (∀ q ∈ qs, q ∈ I) ∧ qs.length = rs.length ∧
      Ideal.ofList (qs.map (algebraMap R (Localization.Away a))) =
        I.map (algebraMap R (Localization.Away a)) ∧
      RingTheory.Sequence.IsRegular U ((qs.map (algebraMap R (Localization.AtPrime P))).map φ) := by
  obtain ⟨qs, hqs, hlen, heq, hreg'⟩ := I.exists_numerators_of_regular_image P.primeCompl rs φ
    (fun x hx ↦ hgen ▸ Ideal.subset_span hx) hreg
  have hJI : Ideal.ofList qs ≤ I := Ideal.span_le.mpr hqs
  have hlocal : I.map (algebraMap R (Localization.AtPrime P)) =
      (Ideal.ofList qs).map (algebraMap R (Localization.AtPrime P)) := by
    rw [Ideal.map_ofList, heq, hgen]
  obtain ⟨a, ha, haway⟩ := exists_away_map_eq_of_atPrime P I (Ideal.ofList qs) hI hJI hlocal
  exact ⟨a, qs, ha, hqs, hlen, (Ideal.map_ofList _ qs).symm.trans haway.symm, hreg'⟩

end Ideal
