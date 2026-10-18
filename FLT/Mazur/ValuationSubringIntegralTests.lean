/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Valuation witnesses for nonintegral field elements

Integral closure is the intersection of valuation subrings containing the
actual scalar image. Failure constructs a valuation with a coordinate pole.
The scalar map need not be injective and its source need not be a domain.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.ValuationSubringIntegralTests
variable {R K : Type*} [CommRing R] [Field K]

/-- Integral closure in a field is detected by all containing valuation subrings. -/
theorem integral_iff_valuation_subrings (A : Subring K) (x : K) :
    IsIntegral A x ↔ ∀ V : ValuationSubring K, A ≤ V.toSubring → x ∈ V := by
  have he := iInf_valuationSubring_superset (s := (A : Set K))
  rw [Subring.closure_eq] at he
  change x ∈ (integralClosure A K).toSubring ↔ _
  rw [← he, Subring.mem_iInf]
  exact Subtype.forall

/-- Passing to the actual scalar image preserves the monic-equation test. -/
theorem integralElem_iff_range (s : R →+* K) (x : K) :
    s.IsIntegralElem x ↔ IsIntegral s.range x := by
  let _ := s.rangeRestrict.toAlgebra
  let _ := s.toAlgebra
  have : IsScalarTower R s.range K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨fun h ↦ IsIntegral.tower_top h, fun h ↦ ?_⟩
  let _ : Algebra.IsIntegral R s.range :=
    ⟨s.rangeRestrict.isIntegral_of_surjective s.rangeRestrict_surjective⟩
  exact isIntegral_trans (R := R) x h

/-- A field element is integral precisely when every scalar-containing valuation contains it. -/
theorem integralElem_iff_valuation_subrings (s : R →+* K) (x : K) :
    s.IsIntegralElem x ↔ ∀ V : ValuationSubring K, s.range ≤ V.toSubring → x ∈ V := by
  rw [integralElem_iff_range, integral_iff_valuation_subrings]

/-- Nonintegrality constructs a valuation containing all scalars but excluding the element. -/
theorem exists_valuation_of_not_integral (s : R →+* K) (x : K)
    (h : ¬ s.IsIntegralElem x) :
    ∃ V : ValuationSubring K, s.range ≤ V.toSubring ∧ x ∉ V := by
  classical
  simpa only [not_forall, not_imp, exists_prop] using
    h.imp (integralElem_iff_valuation_subrings s x).mpr

end FLT.Mazur.ValuationSubringIntegralTests
