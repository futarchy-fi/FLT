/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineScalarBoundaryNilpotence
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Component equations on the full original boundary product

The minimal prime quotients test nilpotence without a Noetherian hypothesis
on either scalar ring. Their equations recover a common power equation in the
unchanged product, so its nilpotents are retained rather than discarded.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)

/-- The actual point of the unchanged product corresponding to a minimal coordinate prime. -/
def boundaryComponentPoint (Q : minimalPrimes C) : boundaryProduct s κ :=
  (boundaryProduct s κ).isoSpec.inv ⟨Q.val, Q.property.1.1⟩

/-- A component equation is exactly vanishing at its actual original product point. -/
theorem boundaryComponent_equation_iff (Q : minimalPrimes C) (b : B) :
    Ideal.Quotient.mk Q.val (boundaryCoordinate s κ b) = 0 ↔
      b ∈ (boundaryProjection s κ (boundaryComponentPoint s κ Q)).asIdeal := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have h : boundaryCoordinate s κ b ∉ Q.val ↔
      b ∉ (boundaryProjection s κ (boundaryComponentPoint s κ Q)).asIdeal := by
    change (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C) ∈
      PrimeSpectrum.basicOpen (boundaryCoordinate s κ b) ↔ _
    have he : (boundaryProduct s κ).isoSpec.hom (boundaryComponentPoint s κ Q) =
        (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C) :=
      congrArg (fun f ↦ f (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C))
        (boundaryProduct s κ).isoSpec.inv_hom_id
    rw [← he]
    change boundaryComponentPoint s κ Q ∈
      (boundaryProduct s κ).toSpecΓ ⁻¹ᵁ
        PrimeSpectrum.basicOpen (boundaryCoordinate s κ b) ↔ _
    rw [Scheme.toSpecΓ_preimage_basicOpen]
    rw [boundaryCoordinate_basicOpen]
    rfl
  exact not_iff_not.mp h

/-- Minimal component equations detect nilpotence on the full original product. -/
theorem boundaryCoordinate_nilpotent_iff_components (b : B) :
    IsNilpotent (boundaryCoordinate s κ b) ↔
      ∀ Q : minimalPrimes C, Ideal.Quotient.mk Q.val (boundaryCoordinate s κ b) = 0 := by
  rw [← mem_nilradical, nilradical, ← Ideal.sInf_minimalPrimes]
  simp only [Ideal.mem_sInf, Ideal.Quotient.eq_zero_iff_mem, Subtype.forall]
  rfl

/-- The component quotients supply one exact power equation for any fixed finite test family. -/
theorem boundary_components_iff_common_power (a : Finset B) :
    (∀ Q : minimalPrimes C, ∀ b ∈ a,
      Ideal.Quotient.mk Q.val (boundaryCoordinate s κ b) = 0) ↔
      ∃ n : ℕ, ∀ b ∈ a, boundaryCoordinate s κ b ^ n = 0 := by
  classical
  constructor
  · intro h
    have hn (b : a) : IsNilpotent (boundaryCoordinate s κ b.val) :=
      (boundaryCoordinate_nilpotent_iff_components s κ b.val).mpr
        (fun Q ↦ h Q b.val b.property)
    choose n hn using hn
    refine ⟨Finset.univ.sup n, fun b hb ↦ ?_⟩
    exact pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ (⟨b, hb⟩ : a))) (hn ⟨b, hb⟩)
  · rintro ⟨n, hn⟩ Q b hb
    exact (boundaryCoordinate_nilpotent_iff_components s κ b).mp ⟨n, hn b hb⟩ Q

/-- A failed boundary equation already fails on a minimal domain component. -/
theorem exists_boundary_component_nonzero (b : B)
    (h : ¬ IsNilpotent (boundaryCoordinate s κ b)) :
    ∃ Q : minimalPrimes C, Ideal.Quotient.mk Q.val (boundaryCoordinate s κ b) ≠ 0 := by
  simpa only [not_forall] using h.imp (boundaryCoordinate_nilpotent_iff_components s κ b).mpr

end FLT.Mazur.AffineScalarBoundaryNilpotence
