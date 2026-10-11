/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Principal neighborhoods of finite sets inside affine envelopes

Prime avoidance produces one principal open containing an entire finite set
and avoiding a prescribed closed boundary. Pulling it back along an open
immersion gives an affine neighborhood in the original scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineEnvelopeFiniteNeighborhood
universe u
set_option backward.isDefEq.respectTransparency false

/-- One principal open in an affine spectrum contains a finite set inside a prescribed open. -/
theorem exists_principal {A : Type u} [CommRing A]
    (W : TopologicalSpace.Opens (PrimeSpectrum A)) (s : Set (PrimeSpectrum A))
    (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ a : A, s ⊆ (PrimeSpectrum.basicOpen a : Set _) ∧ PrimeSpectrum.basicOpen a ≤ W := by
  classical
  let J := PrimeSpectrum.vanishingIdeal (W : Set (PrimeSpectrum A))ᶜ
  have hJ (x : PrimeSpectrum A) (hx : x ∈ W) : ¬ J ≤ x.asIdeal := by
    intro h
    have hz : x ∈ PrimeSpectrum.zeroLocus (J : Set A) := h
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      W.isOpen.isClosed_compl.closure_eq] at hz
    exact hz hx
  have hn : ¬ (J : Set A) ⊆ ⋃ P ∈ PrimeSpectrum.asIdeal '' s, (P : Set A) := by
    rw [Ideal.subset_union_prime_finite (hs.image _) (⊥ : Ideal A) ⊥]
    · rintro ⟨P, ⟨x, hx, rfl⟩, h⟩
      exact hJ x (hsW hx) h
    · rintro P ⟨x, _, rfl⟩ _ _
      exact x.isPrime
  obtain ⟨a, ha, hn⟩ := Set.not_subset.mp hn
  refine ⟨a, ?_, ?_⟩
  · intro x hx hax
    exact hn (Set.mem_iUnion₂.mpr ⟨x.asIdeal, ⟨x, hx, rfl⟩, hax⟩)
  · intro x hx
    by_contra hxW
    exact hx ((PrimeSpectrum.mem_vanishingIdeal _ _).mp ha x hxW)

/-- The actual affine envelope supplies a principal neighborhood, without ampleness assumptions. -/
theorem exists_envelope_principal {Y : Scheme.{u}} [IsAffine Y]
    (W : Y.Opens) (s : Set Y) (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ a : Γ(Y, ⊤), s ⊆ Y.basicOpen a ∧ Y.basicOpen a ≤ W := by
  obtain ⟨a, ha, haW⟩ := exists_principal (Y.isoSpec.hom ''ᵁ W)
    (Y.isoSpec.hom '' s) (hs.image _) (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hsW hx, rfl⟩)
  refine ⟨a, ?_, ?_⟩
  · intro x hx
    have h := ha (Set.mem_image_of_mem Y.isoSpec.hom hx)
    change x ∈ Y.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen a at h
    rwa [Scheme.toSpecΓ_preimage_basicOpen] at h
  · have h := (TopologicalSpace.Opens.map Y.isoSpec.hom.base).monotone haW
    rwa [Y.isoSpec.hom.preimage_image_eq, Scheme.isoSpec_hom,
      Scheme.toSpecΓ_preimage_basicOpen] at h

/-- Every finite set in an open subscheme of an affine scheme has an actual affine neighborhood. -/
theorem exists_affineOpen {Z Y : Scheme.{u}} [IsAffine Y]
    (j : Z ⟶ Y) [IsOpenImmersion j] (W : Z.Opens)
    (s : Set Z) (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ U : Z.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W := by
  obtain ⟨a, ha, haW⟩ := exists_envelope_principal (j ''ᵁ W) (j '' s) (hs.image _)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hsW hx, rfl⟩)
  refine ⟨j ⁻¹ᵁ Y.basicOpen a, ?_, ?_, ?_⟩
  · exact ((isAffineOpen_top Y).basicOpen a).preimage_of_isOpenImmersion j
      (haW.trans (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩))
  · intro x hx
    exact ha (Set.mem_image_of_mem j hx)
  · rw [← j.preimage_image_eq W]
    exact (TopologicalSpace.Opens.map j.base).monotone haW

end FLT.Mazur.AffineEnvelopeFiniteNeighborhood
