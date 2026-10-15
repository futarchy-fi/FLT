/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianClosedImageGenerizations
public import FLT.Mazur.SchemeOpenEnvelopeInterior
public import Mathlib.AlgebraicGeometry.Properties

/-!
# The denominator ideal is a finite intersection of actual source primes

The generic points of the excluded envelope give finitely many primes in the
original source section ring. Their intersection is exactly the denominator
ideal, not merely its radical. No closedness of the projection is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {Y X : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens)

/-- A global coefficient avoids a source point exactly when it belongs to its section prime. -/
theorem not_mem_basicOpen_iff_sectionPrime (r : Γ(X, ⊤)) (x : X) :
    x ∉ X.basicOpen r ↔ r ∈ (X.toSpecΓ x).asIdeal := by
  have h : x ∈ X.basicOpen r ↔ r ∉ (X.toSpecΓ x).asIdeal := by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    rfl
  exact h.not.trans not_not

/-- Any dense family of excluded points computes the entire denominator ideal. -/
theorem denominatorIdeal_eq_generic_primes (F : Set Y)
    (hF : closure F = (O : Set Y)ᶜ) :
    denominatorIdeal π.appTop.hom O = ⨅ e ∈ F, (X.toSpecΓ (π e)).asIdeal := by
  ext r
  simp only [Ideal.mem_iInf]
  constructor
  · intro hr e he
    apply (not_mem_basicOpen_iff_sectionPrime r (π e)).mp
    intro hx
    have hy : e ∈ Y.basicOpen (π.appTop.hom r) := by
      rwa [← Scheme.Hom.preimage_basicOpen_top]
    exact (hF ▸ subset_closure he) ((mem_denominatorIdeal _ _ _).mp hr hy)
  · intro hr
    rw [mem_denominatorIdeal, ← Scheme.Hom.preimage_basicOpen_top]
    intro e he
    by_contra hn
    have hsub : F ⊆ (π ⁻¹' (X.basicOpen r : Set X))ᶜ := by
      intro y hy
      exact (not_mem_basicOpen_iff_sectionPrime r (π y)).mpr (hr y hy)
    have hc := closure_minimal hsub
      ((X.basicOpen r).isOpen.preimage π.continuous).isClosed_compl
    exact hc (hF.symm ▸ hn) he

variable [NoetherianSpace Y]

/-- Construct a finite intersection presentation using actual excluded envelope coordinates. -/
theorem exists_finite_denominator_primes :
    ∃ F : Set Y, F.Finite ∧ F ⊆ (O : Set Y)ᶜ ∧
      closure F = (O : Set Y)ᶜ ∧
      denominatorIdeal π.appTop.hom O = ⨅ e ∈ F, (X.toSpecΓ (π e)).asIdeal := by
  obtain ⟨F, hF, hFO, hc⟩ :=
    NoetherianClosedImage.exists_finite_generics O.isOpen.isClosed_compl
  exact ⟨F, hF, hFO, hc, denominatorIdeal_eq_generic_primes π O F hc⟩

end FLT.Mazur.SchemeOpenEnvelope
