/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismPrincipalCover

/-!
# Finite principal chart refinements of an arbitrary affine test

Compactness selects finitely many actual chart refinements covering the coefficient
spectrum. Their coefficients generate the unit ideal, including for the zero ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)

/-- Finitely many actual pulled-back chart refinements cover every coefficient prime. -/
theorem exists_ambientMorphismFiniteCover :
    ∃ s : Finset (AmbientMorphismCoverIndex f),
      ∀ p : PrimeSpectrum A, ∃ q ∈ s, p ∈ PrimeSpectrum.basicOpen q.2.val := by
  have hc : (Set.univ : Set (PrimeSpectrum A)) ⊆
      ⋃ q : AmbientMorphismCoverIndex f,
        (PrimeSpectrum.basicOpen q.2.val : Set (PrimeSpectrum A)) := by
    intro p _
    obtain ⟨q, hq⟩ := ambientMorphismCover_exists f p
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  obtain ⟨s, hs⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (PrimeSpectrum A))).elim_finite_subcover
    (fun q : AmbientMorphismCoverIndex f ↦
      (PrimeSpectrum.basicOpen q.2.val : Set (PrimeSpectrum A)))
    (fun q ↦ (PrimeSpectrum.basicOpen q.2.val).isOpen) hc
  refine ⟨s, fun p ↦ ?_⟩
  simpa only [Set.mem_iUnion, exists_prop, SetLike.mem_coe] using hs (Set.mem_univ p)

/-- A selected finite set of genuine chart refinements; no quotient or descent is assumed. -/
def ambientMorphismFiniteCoverIndices : Finset (AmbientMorphismCoverIndex f) :=
  (exists_ambientMorphismFiniteCover f).choose

/-- The selected finite chart refinements retain coverage of every coefficient prime. -/
theorem ambientMorphismFiniteCover_covers (p : PrimeSpectrum A) :
    ∃ q ∈ ambientMorphismFiniteCoverIndices f, p ∈ PrimeSpectrum.basicOpen q.2.val :=
  (exists_ambientMorphismFiniteCover f).choose_spec p

/-- The finite refinement coefficients generate the unit ideal needed for module descent. -/
theorem ambientMorphismFiniteCover_span :
    Ideal.span (Set.range (fun q : ambientMorphismFiniteCoverIndices f ↦ q.val.2.val)) = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
  let _ := hp.isPrime
  obtain ⟨q, hq, hr⟩ := ambientMorphismFiniteCover_covers f ⟨p, inferInstance⟩
  exact hr (hle (Ideal.subset_span ⟨⟨q, hq⟩, rfl⟩))

/-- The finite coefficient principal chart cover, with its actual localization morphisms. -/
def ambientMorphismFinitePrincipalCover : (Spec (.of A)).OpenCover where
  I₀ := ambientMorphismFiniteCoverIndices f
  X q := Spec (.of (Localization.Away q.val.2.val))
  f q := Spec.algebraMap A (Localization.Away q.val.2.val)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p ↦ ?_, fun q ↦ inferInstance⟩
    obtain ⟨q, hq, hr⟩ := ambientMorphismFiniteCover_covers f p
    refine ⟨⟨q, hq⟩, (basicOpenIsoSpecAway (R := .of A) q.2.val).hom ⟨p, hr⟩, ?_⟩
    exact congrArg (fun g ↦ g ⟨p, hr⟩)
      (basicOpenIsoSpecAway_hom_SpecMap (R := .of A) q.2.val)

end FLT.Mazur.GrassmannianChart
