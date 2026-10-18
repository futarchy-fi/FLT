/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarFiniteBadPrimes
public import FLT.Mazur.SchemeOpenEnvelopeDenominators

/-!
# Original denominators from the actual finite bad primes

The denominator ideal is the intersection of contractions of finitely many
actual bad points. A product of separating coefficients gives a single original
principal neighborhood. This keeps the original ring even for nonaffine sources.
-/

@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme}
  (s : R →+* Γ(X, ⊤)) (O : X.Opens)

/-- Dense actual bad points compute the exact original denominator ideal. -/
theorem denominatorIdeal_eq_scalar_generic_primes (F : Set X)
    (hF : closure F = (O : Set X)ᶜ) :
    denominatorIdeal s O = ⨅ x ∈ F, (scalarMorphism s x).asIdeal := by
  ext r
  simp only [Ideal.mem_iInf]
  constructor
  · intro hr x hx
    by_contra hn
    have hmem : x ∈ X.basicOpen (s r) := by
      rw [← scalarMorphism_preimage]
      exact hn
    exact (hF ▸ subset_closure hx) (hr hmem)
  · intro hr x hx
    by_contra hn
    have hsub : F ⊆ (X.basicOpen (s r) : Set X)ᶜ := by
      intro y hy hmem
      have hpre : y ∈ scalarMorphism s ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
        rwa [scalarMorphism_preimage]
      exact hpre (hr y hy)
    have hcl := closure_minimal hsub (X.basicOpen (s r)).isOpen.isClosed_compl
    exact hcl (hF.symm ▸ hn) hx

/-- The original denominator ideal has a finite intersection presentation with actual bad points. -/
theorem exists_finite_scalar_denominator_primes [NoetherianSpace X] :
    ∃ F : Set X, F.Finite ∧ F ⊆ (O : Set X)ᶜ ∧
      closure F = (O : Set X)ᶜ ∧
      denominatorIdeal s O = ⨅ x ∈ F, (scalarMorphism s x).asIdeal := by
  obtain ⟨F, hfin, hFO, hc⟩ :=
    NoetherianClosedImage.exists_finite_generics O.isOpen.isClosed_compl
  exact ⟨F, hfin, hFO, hc, denominatorIdeal_eq_scalar_generic_primes s O F hc⟩

/-- Multiplying one separator per bad prime constructs a full original principal neighborhood. -/
theorem scalar_badPrime_product (F : Finset X)
    (hF : closure (F : Set X) = (O : Set X)ᶜ) (P : PrimeSpectrum R)
    (a : X → R) (ha : ∀ x ∈ F, a x ∈ (scalarMorphism s x).asIdeal ∧ a x ∉ P.asIdeal) :
    (∏ x ∈ F, a x) ∉ P.asIdeal ∧ X.basicOpen (s (∏ x ∈ F, a x)) ≤ O := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, hm⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact (ha x hx).2 hm
  · change (∏ x ∈ F, a x) ∈ denominatorIdeal s O
    rw [denominatorIdeal_eq_scalar_generic_primes s O (F : Set X) hF]
    simp only [Ideal.mem_iInf, Finset.mem_coe]
    intro x hx
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hx) (ha x hx).1

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
