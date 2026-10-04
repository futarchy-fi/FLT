/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PolynomialLocalDimension
public import FLT.Mathlib.RingTheory.Regular.ParameterSequence

/-! # The parameter criterion in a rational polynomial local ring -/

@[expose] public section

namespace MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-- Any n equations with nonzero Artinian quotient at a rational point form a regular sequence. -/
theorem isRegular_parameters_at_rationalPoint (a : Fin n → k)
    (rs : List (Localization.AtPrime (rationalPointIdeal a))) (hlen : rs.length = n)
    [IsArtinianRing (Localization.AtPrime (rationalPointIdeal a) ⧸ Ideal.ofList rs)]
    [Nontrivial (Localization.AtPrime (rationalPointIdeal a) ⧸ Ideal.ofList rs)] :
    RingTheory.Sequence.IsRegular (Localization.AtPrime (rationalPointIdeal a)) rs := by
  have hproper : Ideal.ofList rs ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  apply RingTheory.Sequence.isRegular_of_artinian_quotient_of_full_length rs
    (fun r hr ↦ IsLocalRing.le_maximalIdeal hproper (Ideal.subset_span hr))
  refine ⟨(List.finRange n).map (fun i ↦
    algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime (rationalPointIdeal a))
      (X i - C (a i))), ?_, isRegular_localized_X_sub_C a⟩
  simp [hlen]

end MvPolynomial
