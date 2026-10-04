/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.TranslatedVariables
public import FLT.Mathlib.RingTheory.Regular.LengthBound
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-! # Dimension and a full regular sequence at a rational polynomial point -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-- The maximal ideal of a rational point. -/
abbrev rationalPointIdeal (a : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (aeval a)

instance rationalPointIdeal_isMaximal (a : Fin n → k) : (rationalPointIdeal a).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c ↦ ⟨C c, by simp⟩)

/-- The ordered variable differences are regular in the local ring at a rational point. -/
theorem isRegular_localized_X_sub_C (a : Fin n → k) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime (rationalPointIdeal a))
      ((List.finRange n).map fun i ↦
        algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime (rationalPointIdeal a))
          (X i - C (a i))) := by
  have h := (isRegular_X_sub_C_list a (List.nodup_finRange n)).toIsWeaklyRegular
  have hmem : ∀ f ∈ (List.finRange n).map (fun i ↦ X i - C (a i)),
      f ∈ rationalPointIdeal a := by
    intro f hf
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
    simp [rationalPointIdeal]
  simpa only [List.map_map, Function.comp_def] using
    h.isRegular_of_isLocalization_of_mem (Localization.AtPrime (rationalPointIdeal a))
      (rationalPointIdeal a) hmem

/-- A rational point of affine n-space has local dimension n. -/
theorem ringKrullDim_at_rationalPoint (a : Fin n → k) :
    ringKrullDim (Localization.AtPrime (rationalPointIdeal a)) = n := by
  apply le_antisymm
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height (rationalPointIdeal a)]
    have h := (rationalPointIdeal a).height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    simpa using h
  · simpa using (isRegular_localized_X_sub_C a).length_le_ringKrullDim

/-- Every regular sequence at the rational point has length at most n. -/
theorem regularSequence_length_le_at_rationalPoint (a : Fin n → k)
    {rs : List (Localization.AtPrime (rationalPointIdeal a))}
    (h : RingTheory.Sequence.IsRegular (Localization.AtPrime (rationalPointIdeal a)) rs) :
    rs.length ≤ n :=
  h.length_le_of_ringKrullDim_eq (ringKrullDim_at_rationalPoint a)

end MvPolynomial
