/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeTranslationNormFiber
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Constructed local bases for finite flat translation norms

Finite presentation and flatness produce genuine finite bases after principal
coefficient localization. The construction applies to finite etale algebras
over a noetherian base and does not assume that they are globally free.
-/

@[expose] public noncomputable section
open Module TensorProduct
namespace FLT.Mazur.FiniteFreeTranslationNorm
universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Finite presented flat translations have finite bases on principal neighborhoods. -/
theorem exists_principal_basis [Module.FinitePresentation R S] [Module.Flat R S]
    (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r) (Localization.Away r ⊗[R] S)) := by
  let P := Localization.AtPrime p.asIdeal
  let _ : Module.Free P (P ⊗[R] S) := Module.free_of_flat_of_isLocalRing
  let _ : Module.Free P (LocalizedModule.AtPrime p.asIdeal S) :=
    Module.Free.of_equiv (LocalizedModule.isBaseChange p.asIdeal.primeCompl S).equiv
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl S) P
  let _ := (show Localization.Away r →+* P from
    IsLocalization.map (M := .powers r) (T := p.asIdeal.primeCompl) P
      (RingHom.id R) (Submonoid.powers_le.mpr hr)).domain_nontrivial
  let _ := hfree
  let _ : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] S) :=
    Module.Free.of_equiv (LocalizedModule.isBaseChange (Submonoid.powers r) S).equiv.symm
  exact ⟨r, hr, _, ⟨Module.finBasis _ _⟩⟩

/-- Noetherian finite etale translations supply the finite-presentation hypothesis themselves. -/
theorem exists_etale_principal_basis [IsNoetherianRing R] [Module.Finite R S]
    [Algebra.Etale R S] (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r) (Localization.Away r ⊗[R] S)) := by
  let _ := Module.finitePresentation_of_finite R S
  exact exists_principal_basis p

/-- Every coefficient on a constructed local translation has a genuine full-fiber norm. -/
theorem exists_etale_norm_chart [IsNoetherianRing R] [Module.Finite R S]
    [Algebra.Etale R S] (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ n : ℕ,
      ∃ _b : Basis (Fin n) (Localization.Away r) (Localization.Away r ⊗[R] S),
      ∀ (s : Localization.Away r ⊗[R] S) (q : PrimeSpectrum (Localization.Away r)),
        q ∈ PrimeSpectrum.basicOpen (Algebra.norm (Localization.Away r) s) ↔
          ∀ z : PrimeSpectrum (Localization.Away r ⊗[R] S),
            PrimeSpectrum.comap (algebraMap _ _) z = q → z ∈ PrimeSpectrum.basicOpen s := by
  obtain ⟨r, hr, n, ⟨b⟩⟩ := exists_etale_principal_basis (S := S) p
  exact ⟨r, hr, n, b, fun s q ↦ mem_basicOpen_norm_iff b q s⟩

end FLT.Mazur.FiniteFreeTranslationNorm
