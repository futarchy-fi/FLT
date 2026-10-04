/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundle
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Spreading a regular ideal generator to a principal neighborhood

A rank-one basis of a finitely presented ideal at a localization spreads to
one principal localization. The image of one under the resulting equivalence
is a regular generator because the ideal inclusion is injective.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve
variable {R : Type*} [CommRing R]

/-- An ideal isomorphic to its coefficient ring has a regular principal equation. -/
theorem regular_generator_of_ideal_equiv (I : Ideal R) (e : R ≃ₗ[R] I) :
    ∃ a : R, IsRegular a ∧ I = Ideal.span {a} := by
  have he (r : R) : (e r).val = r * (e 1).val := by
    simpa using congrArg Subtype.val (e.map_smul r (1 : R))
  refine ⟨(e 1).val, ?_, ?_⟩
  · rw [← isRightRegular_iff_isRegular]
    intro x y h
    apply e.injective
    apply Subtype.ext
    rw [he x, he y]
    exact h
  · apply le_antisymm
    · intro x hx
      obtain ⟨r, hr⟩ := e.surjective ⟨x, hx⟩
      rw [Ideal.mem_span_singleton]
      refine ⟨r, ?_⟩
      have hval := congrArg Subtype.val hr
      rw [he r] at hval
      exact hval.symm.trans (mul_comm _ _)
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (e 1).property)

/-- A localized rank-one ideal basis of a finitely presented ideal spreads to
a principal neighborhood. Finite presentation, not just finite generation,
is the hypothesis that permits this passage. -/
theorem ideal_equiv_spreads (I : Ideal R) [Module.FinitePresentation R I]
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (e : A ≃ₗ[A] I.map (algebraMap R A)) :
    ∃ r ∈ S, Nonempty (Localization.Away r ≃ₗ[Localization.Away r]
      I.map (algebraMap R (Localization.Away r))) := by
  obtain ⟨r, hr, l, _⟩ :=
    Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule S
      (Algebra.linearMap R A) (Algebra.idealMap A I) (e.restrictScalars R)
  let er := (IsLocalizedModule.iso (.powers r)
    (Algebra.linearMap R (Localization.Away r))).extendScalarsOfIsLocalization
      (.powers r) (Localization.Away r)
  let ei := (IsLocalizedModule.iso (.powers r)
    (Algebra.idealMap (Localization.Away r) I)).extendScalarsOfIsLocalization
      (.powers r) (Localization.Away r)
  exact ⟨r, hr, ⟨er.symm ≪≫ₗ l ≪≫ₗ ei⟩⟩

/-- A regular equation at a prime of a finitely presented ideal extends to
an actual regular equation on a principal neighborhood of that prime. -/
theorem ideal_regular_generator_spreads (I : Ideal R) [Module.FinitePresentation R I]
    (p : Ideal R) [p.IsPrime] (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization.AtPrime A p] (a : A) (ha : IsRegular a)
    (hI : I.map (algebraMap R A) = Ideal.span {a}) :
    ∃ r : R, r ∉ p ∧ ∃ b : Localization.Away r, IsRegular b ∧
      I.map (algebraMap R (Localization.Away r)) = Ideal.span {b} := by
  obtain ⟨r, hr, ⟨e⟩⟩ := ideal_equiv_spreads I p.primeCompl A
    (CartierModule.idealEquiv _ a ha hI)
  exact ⟨r, hr, regular_generator_of_ideal_equiv _ e⟩

end FLT.Mazur.FCurve
