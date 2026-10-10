/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesHomogeneous
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The grading and degree-zero principal localizations of the original Rees algebra

The actual ideal-power monomials form an internal direct sum. This supplies
the grading needed by Proj and its homogeneous degree-zero localizations.
No comparison with the fraction atlas is assumed here.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Distinct original Rees degrees are independent, by coefficient extraction. -/
theorem component_independent : iSupIndep (component I) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv he n hn
  have hpoly := congrArg (reesAlgebra I).val he
  rw [map_sum, map_zero] at hpoly
  have hc := congrArg (fun p : A[X] => p.coeff n) hpoly
  have hsum : (∑ i ∈ s, ((v i : reesAlgebra I) : A[X]).coeff n) = 0 := by
    simpa only [finsetSum_coeff, coeff_zero, Subalgebra.val_apply] using hc
  have hncoeff : ((v n : reesAlgebra I) : A[X]).coeff n = 0 := by
    rw [Finset.sum_eq_single n] at hsum
    · exact hsum
    · intro i hi hin
      exact component_coeff_eq_zero I (v i) (hv i hi) (Ne.symm hin)
    · exact fun h => (h hn).elim
  apply Subtype.ext
  rw [component_eq_monomial I n (v n) (hv n hn), hncoeff, map_zero]
  rfl

/-- Every original Rees polynomial is the finite sum of its homogeneous monomials. -/
theorem component_sum (p : reesAlgebra I) :
    ∑ n ∈ (p : A[X]).support, monomialMap I n ⟨(p : A[X]).coeff n, p.property n⟩ = p := by
  apply Subtype.ext
  change (reesAlgebra I).val (∑ n ∈ (p : A[X]).support,
    monomialMap I n ⟨(p : A[X]).coeff n, p.property n⟩) = _
  rw [map_sum]
  exact (p : A[X]).as_sum_support.symm

/-- The homogeneous pieces span the entire actual Rees algebra. -/
theorem component_iSup : (⨆ n, component I n) = ⊤ := by
  apply top_unique
  intro p _
  rw [← component_sum I p]
  exact Submodule.sum_mem _ (fun n _ =>
    Submodule.mem_iSup_of_mem n (monomial_mem_component I n _))

/-- The homogeneous pieces give an actual internal direct sum decomposition. -/
theorem component_internal : DirectSum.IsInternal (component I) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (component_independent I) (component_iSup I)

instance componentGradedRing : GradedRing (component I) where
  toGradedMonoid := component_gradedMonoid I
  toDecomposition := (component_internal I).chooseDecomposition

/-- The original degree-one element f*T corresponding to a member of the center ideal. -/
def generator (f : A) (hf : f ∈ I) : reesAlgebra I :=
  monomialMap I 1 ⟨f, by simpa only [pow_one] using hf⟩

/-- The original center generator is homogeneous of degree one. -/
theorem generator_mem (f : A) (hf : f ∈ I) : generator I f hf ∈ component I 1 :=
  monomial_mem_component I 1 _

/-- The actual degree-zero homogeneous localization at the original Rees generator f*T. -/
abbrev DegreeZeroChart (f : A) (hf : f ∈ I) :=
  HomogeneousLocalization.Away (component I) (generator I f hf)

/-- A degree n numerator divided by the nth power of the original degree-one denominator. -/
def homogeneousFraction (f : A) (hf : f ∈ I) (n : ℕ) (a : ↥(I ^ n)) :
    DegreeZeroChart I f hf :=
  HomogeneousLocalization.Away.mk (component I) (generator_mem I f hf) n (monomialMap I n a)
    (by simpa only [smul_eq_mul, mul_one] using monomial_mem_component I n a)

end FLT.Mazur.BlowupRees
