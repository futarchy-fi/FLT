/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrimeSmoothLocalizationCartier
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth

/-!
# Finite flat ideals in locally smooth curve algebras

A standard-smooth principal cover supplies a compatible chart at every prime.
The full finite flat quotient stays on the original ambient. A presentation
of its ideal spreads the constructed stalk equation to a Cartier neighborhood;
an actual finite quotient basis supplies that presentation automatically.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.FinitePresentation R B]

/-- Local smoothness suffices for regular equations of the full finite flat ideal at primes. -/
theorem regular_generator_locallySmooth_finite_flat_atPrime
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R B))
    (I : Ideal B) [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (q : Ideal B) [q.IsPrime] :
    ∃ a : Localization.AtPrime q, IsRegular a ∧
      I.map (algebraMap B (Localization.AtPrime q)) = Ideal.span {a} := by
  obtain ⟨S, hS, hchart⟩ := h
  obtain ⟨s, hs, hsq⟩ : ∃ s ∈ S, s ∉ q := by
    by_contra hn
    push Not at hn
    have hle : Ideal.span S ≤ q := Ideal.span_le.mpr hn
    rw [hS] at hle
    exact (inferInstance : q.IsPrime).ne_top (top_le_iff.mp hle)
  have hsm := hchart s hs
  rw [← IsScalarTower.algebraMap_eq R B (Localization.Away s),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hsm
  let _ := hsm
  exact regular_generator_smooth_away_finite_flat_atPrime (R := R) I q s hsq

/-- A presented finite flat ideal on a locally smooth curve has principal Cartier neighborhoods. -/
theorem cartier_neighborhood_locallySmooth_finite_flat
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R B))
    (I : Ideal B) [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    [Module.FinitePresentation B I] (q : Ideal B) [q.IsPrime] :
    ∃ s : B, s ∉ q ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  obtain ⟨a, ha, hIa⟩ := regular_generator_locallySmooth_finite_flat_atPrime h I q
  exact ideal_regular_generator_spreads I q (Localization.AtPrime q) a ha hIa

/-- An actual finite basis of the quotient removes the ideal-presentation hypothesis. -/
theorem cartier_neighborhood_locallySmooth_quotient_basis
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R B))
    (I : Ideal B) {d : ℕ} (b : Module.Basis (Fin d) R (B ⧸ I))
    (q : Ideal B) [q.IsPrime] :
    ∃ s : B, s ∉ q ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  let _ : Module.Free R (B ⧸ I) := Module.Free.of_basis b
  let _ : Module.Finite R (B ⧸ I) := Module.Finite.of_basis b
  let _ := ideal_finitePresentation_of_quotient_basis I b
  exact cartier_neighborhood_locallySmooth_finite_flat h I q

end FLT.Mazur.FCurve
