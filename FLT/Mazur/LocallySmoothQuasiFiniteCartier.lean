/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrimeQuasiFiniteSmoothCartier
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth

/-!
# Cartier neighborhoods for quasi-finite flat ideals on smooth curves

Locally standard-smooth coordinates suffice for every finitely presented
ideal with flat quasi-finite quotient. Over a Noetherian coefficient ring,
the required ideal presentation is automatic.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Local smoothness constructs regular equations of the full quasi-finite flat ideal. -/
theorem regular_generator_locallySmooth_quasiFinite_flat_atPrime
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R B))
    (I : Ideal B) [Algebra.QuasiFinite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    [Module.FinitePresentation B I] (q : Ideal B) [q.IsPrime] :
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
  exact regular_generator_smooth_away_quasiFinite_flat_atPrime (R := R) I q s hsq

/-- A presented quasi-finite flat ideal on a smooth curve has Cartier neighborhoods. -/
theorem cartier_neighborhood_locallySmooth_quasiFinite_flat
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R B))
    (I : Ideal B) [Algebra.QuasiFinite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    [Module.FinitePresentation B I] (q : Ideal B) [q.IsPrime] :
    ∃ s : B, s ∉ q ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  obtain ⟨a, ha, hIa⟩ := regular_generator_locallySmooth_quasiFinite_flat_atPrime h I q
  exact ideal_regular_generator_spreads I q (Localization.AtPrime q) a ha hIa

/-- Noetherian coefficients supply the ideal presentation for quasi-finite flat families. -/
theorem cartier_neighborhood_locallySmooth_quasiFinite_flat_noetherian
    [IsNoetherianRing R] [Algebra.FiniteType R B]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R B))
    (I : Ideal B) [Algebra.QuasiFinite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (q : Ideal B) [q.IsPrime] :
    ∃ s : B, s ∉ q ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  let _ : Module.FinitePresentation B I := Module.finitePresentation_of_finite B I
  exact cartier_neighborhood_locallySmooth_quasiFinite_flat h I q

end FLT.Mazur.FCurve
