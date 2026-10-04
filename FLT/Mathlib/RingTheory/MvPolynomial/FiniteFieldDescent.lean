/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.FaithfullyFlatDescent
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Descent of polynomial relation lists to a finite field extension -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k Ω σ : Type*} [Field k] [Field Ω] [Algebra k Ω]

attribute [local instance] algebraMvPolynomial

/-- Extending the coefficient field preserves and reflects regular polynomial lists. -/
theorem isRegular_map_field_iff (rs : List (MvPolynomial σ k)) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ Ω) (rs.map (map (algebraMap k Ω))) ↔
      RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs := by
  let e := Algebra.IsPushout.equiv k (MvPolynomial σ k) Ω (MvPolynomial σ Ω)
  have : Module.FaithfullyFlat (MvPolynomial σ k) (MvPolynomial σ Ω) :=
    Module.FaithfullyFlat.of_linearEquiv _ _ e.symm.toLinearEquiv
  exact RingTheory.Sequence.isRegular_iff_of_faithfullyFlat

/-- A finite polynomial list over an algebraic extension is defined over a finite subextension. -/
theorem exists_finite_field_of_polynomial_list [Algebra.IsAlgebraic k Ω]
    (rs : List (MvPolynomial σ Ω)) :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧
      ∃ qs : List (MvPolynomial σ E), qs.map (map (algebraMap E Ω)) = rs := by
  classical
  let c : Finset Ω := rs.toFinset.biUnion coeffs
  let E := IntermediateField.adjoin k (c : Set Ω)
  have hE : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin
    (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  have hmap (f : MvPolynomial σ Ω) (hf : f ∈ rs) :
      f ∈ Set.range (map (algebraMap E Ω)) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    have hxE : x ∈ E := IntermediateField.subset_adjoin k _
      (Finset.mem_biUnion.mpr ⟨f, List.mem_toFinset.mpr hf, hx⟩)
    exact ⟨⟨x, hxE⟩, rfl⟩
  have liftList (xs : List (MvPolynomial σ Ω))
      (hx : ∀ f ∈ xs, f ∈ Set.range (map (algebraMap E Ω))) :
      ∃ qs : List (MvPolynomial σ E), qs.map (map (algebraMap E Ω)) = xs := by
    induction xs with
    | nil => exact ⟨[], rfl⟩
    | cons f xs ih =>
      obtain ⟨q, hq⟩ := hx f (by simp)
      obtain ⟨qs, hqs⟩ := ih (fun f hf ↦ hx f (by simp [hf]))
      exact ⟨q :: qs, by simp [hq, hqs]⟩
  exact ⟨E, hE, liftList rs hmap⟩

/-- Regular polynomial relations descend together with their coefficients. -/
theorem exists_finite_field_of_regular_list [Algebra.IsAlgebraic k Ω]
    {rs : List (MvPolynomial σ Ω)} (h : RingTheory.Sequence.IsRegular (MvPolynomial σ Ω) rs) :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧
      ∃ qs : List (MvPolynomial σ E), qs.map (map (algebraMap E Ω)) = rs ∧
        RingTheory.Sequence.IsRegular (MvPolynomial σ E) qs := by
  obtain ⟨E, hE, qs, hqs⟩ := exists_finite_field_of_polynomial_list (k := k) rs
  refine ⟨E, hE, qs, hqs, (isRegular_map_field_iff (Ω := Ω) qs).mp ?_⟩
  rwa [hqs]

end MvPolynomial
