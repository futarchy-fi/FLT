/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousPrimeAvoidance
public import FLT.Mazur.ProjectiveFiniteAvoidance
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Common affine neighborhoods in Proj

Every finite set in an open subset of Proj lies in a single positive homogeneous
basic open contained in that subset. The basic open is an actual affine scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry

namespace FLT.Mazur.ProjectiveFiniteNeighborhood

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A positive homogeneous principal open contains a finite set and avoids the boundary. -/
theorem exists_basicOpen (U : (Proj 𝒜).Opens) (s : Finset (Proj 𝒜))
    (hs : ∀ x ∈ s, x ∈ U) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧
      (∀ x ∈ s, x ∈ Proj.basicOpen 𝒜 f) ∧ Proj.basicOpen 𝒜 f ≤ U := by
  classical
  let J := ProjectiveSpectrum.vanishingIdeal (𝒜 := 𝒜) (U : Set (Proj 𝒜))ᶜ
  let I := HomogeneousIdeal.irrelevant 𝒜 ⊓ J
  have hJ (x : Proj 𝒜) (hx : x ∈ U) : ¬ J ≤ x.asHomogeneousIdeal := by
    intro h
    have hz : x ∈ ProjectiveSpectrum.zeroLocus 𝒜 (J : Set A) := h
    rw [ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      U.isOpen.isClosed_compl.closure_eq] at hz
    exact hz hx
  obtain ⟨n, f, hn, hfn, hfI, hf⟩ := HomogeneousAvoidance.exists_positive_avoiding 𝒜 I
    inf_le_left (s.image ProjectiveSpectrum.asHomogeneousIdeal)
    (by rintro P hP; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hP; exact x.isPrime)
    (by
      rintro P hP
      obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp hP
      change ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ⊓ J.toIdeal ≤
        x.asHomogeneousIdeal.toIdeal
      rw [x.isPrime.inf_le]
      exact not_or.mpr ⟨x.not_irrelevant_le, hJ x (hs x hxs)⟩)
  refine ⟨n, f, hn, hfn, ?_, ?_⟩
  · intro x hx
    exact hf _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · intro x hx
    by_contra hxU
    exact hx ((ProjectiveSpectrum.mem_vanishingIdeal _ _).mp hfI.2 x hxU)

/-- The common principal neighborhood is affine, including for the empty finite set. -/
theorem exists_affineOpen (U : (Proj 𝒜).Opens) (s : Finset (Proj 𝒜))
    (hs : ∀ x ∈ s, x ∈ U) :
    ∃ V : (Proj 𝒜).Opens, IsAffineOpen V ∧ (∀ x ∈ s, x ∈ V) ∧ V ≤ U := by
  obtain ⟨n, f, hn, hfn, hfs, hfU⟩ := exists_basicOpen 𝒜 U s hs
  exact ⟨Proj.basicOpen 𝒜 f, Proj.isAffineOpen_basicOpen 𝒜 f hfn hn, hfs, hfU⟩

end FLT.Mazur.ProjectiveFiniteNeighborhood

/-! Common affine neighborhoods in closed projective ambients. -/

open AlgebraicGeometry

universe u v

namespace FLT.Mazur.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {ι : Type v}

/-- Every finite set of projective points lies in one affine open. -/
theorem exists_affineOpen_of_finite (T : Set (space R ι)) (hT : T.Finite) :
    ∃ U : (space R ι).affineOpens, T ⊆ U.val := by
  obtain ⟨n, f, hn, hf, hTf⟩ := exists_homogeneous_avoiding_finite T hT
  exact ⟨⟨Proj.basicOpen (grading R ι) f,
    Proj.isAffineOpen_basicOpen _ f hf hn⟩, hTf⟩

/-- A closed projective embedding supplies common affine neighborhoods of finite sets. -/
theorem exists_affineOpen_of_closed_embedding {Z : Scheme.{max u v}}
    (e : Z ⟶ space R ι) [IsClosedImmersion e] (T : Set Z) (hT : T.Finite) :
    ∃ U : Z.affineOpens, T ⊆ U.val := by
  obtain ⟨U, hU⟩ := exists_affineOpen_of_finite (e '' T) (hT.image e)
  exact ⟨⟨e ⁻¹ᵁ U.val, U.property.preimage e⟩,
    fun x hx ↦ hU (Set.mem_image_of_mem e hx)⟩

end FLT.Mazur.ProjectiveSpace
