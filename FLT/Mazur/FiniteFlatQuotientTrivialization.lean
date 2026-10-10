/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatCoefficientIdeal
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Principal trivializations of finite presented flat quotients

A basis at a coefficient prime spreads to a principal neighborhood. The
trivialization is transported to the actual quotient of the tensor ambient,
so it can be used directly to present the full ideal.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- A presented flat quotient is free on a principal coefficient neighborhood of every prime. -/
theorem exists_free_coefficient_quotient_away (I : Ideal B)
    [Module.FinitePresentation R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ Module.Free (Localization.Away r)
      ((Localization.Away r ⊗[R] B) ⧸
        I.map (Algebra.TensorProduct.includeRight (R := R) (A := Localization.Away r))) := by
  let S := Localization.AtPrime p
  let _ : Module.Free S (S ⊗[R] (B ⧸ I)) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (TensorProduct.mk R S (B ⧸ I) 1) S
  let _ := hf
  let _ : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] (B ⧸ I)) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (.powers r) (B ⧸ I))
  exact ⟨r, hr, Module.Free.of_equiv
    (Algebra.TensorProduct.tensorQuotientEquiv (R := R)
      (Localization.Away r) B (Localization.Away r) I).toLinearEquiv⟩

/-- The coefficient opens carrying actual free quotients cover the entire coefficient spectrum. -/
theorem span_free_coefficient_quotient_away (I : Ideal B)
    [Module.FinitePresentation R (B ⧸ I)] [Module.Flat R (B ⧸ I)] :
    Ideal.span {r : R | Module.Free (Localization.Away r)
      ((Localization.Away r ⊗[R] B) ⧸
        I.map (Algebra.TensorProduct.includeRight (R := R) (A := Localization.Away r)))} = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
  let _ := hp
  obtain ⟨r, hr, hf⟩ := exists_free_coefficient_quotient_away (R := R) I p
  exact hr (hle (Ideal.subset_span hf))

end FLT.Mazur.FCurve
