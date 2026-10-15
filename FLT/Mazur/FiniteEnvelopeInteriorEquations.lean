/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEnvelopeDenominatorPrimes
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite equations and a principal cover of the original envelope interior

On an affine Noetherian source the actual denominator ideal is finitely
generated. Its generators give a finite principal cover of the maximal
full-envelope open and equations for the entire excluded image closure.
No finite or proper projection hypothesis is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {Y X : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens) [IsAffine X]

/-- Every interior point is detected by an actual denominator in the original section ring. -/
theorem mem_interior_iff_exists_denominator (x : X) :
    x ∈ fullFiberInterior π O ↔
      ∃ r ∈ denominatorIdeal π.appTop.hom O, x ∈ X.basicOpen r := by
  constructor
  · intro hx
    obtain ⟨r, hr, hd⟩ := exists_fullFiberInterior_coefficient π O {x}
      (Set.finite_singleton x) (Set.singleton_subset_iff.mpr hx)
    exact ⟨r, hd, hr (Set.mem_singleton x)⟩
  · rintro ⟨r, hr, hx⟩
    exact (basicOpen_le_fullFiberInterior_iff π O r).mpr hr hx

/-- The denominator ideal cuts out precisely the closure of the excluded original image. -/
theorem zeroLocus_denominatorIdeal :
    X.zeroLocus (denominatorIdeal π.appTop.hom O : Set Γ(X, ⊤)) =
      closure (π '' (O : Set Y)ᶜ) := by
  ext x
  have h := mem_interior_iff_exists_denominator π O x
  change x ∈ interior (π '' (O : Set Y)ᶜ)ᶜ ↔ _ at h
  rw [interior_compl] at h
  rw [Scheme.mem_zeroLocus_iff]
  simpa only [Set.mem_compl_iff, SetLike.mem_coe, not_exists, not_and, not_not]
    using h.not.symm

/-- Any generators of the denominator ideal give an exact principal cover of the interior. -/
theorem interior_iff_generator (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = denominatorIdeal π.appTop.hom O) (x : X) :
    x ∈ fullFiberInterior π O ↔ ∃ r ∈ s, x ∈ X.basicOpen r := by
  have hz : X.zeroLocus s = closure (π '' (O : Set Y)ᶜ) := by
    rw [← X.zeroLocus_span s, hs, zeroLocus_denominatorIdeal]
  change x ∈ interior (π '' (O : Set Y)ᶜ)ᶜ ↔ _
  rw [interior_compl, ← hz, Set.mem_compl_iff, Scheme.mem_zeroLocus_iff]
  push Not
  rfl

variable [IsLocallyNoetherian X]

/-- Construct finite original equations and the resulting whole-interior principal cover. -/
theorem exists_finite_interior_equations :
    ∃ s : Finset Γ(X, ⊤),
      Ideal.span (s : Set Γ(X, ⊤)) = denominatorIdeal π.appTop.hom O ∧
      X.zeroLocus (s : Set Γ(X, ⊤)) = closure (π '' (O : Set Y)ᶜ) ∧
      (∀ r ∈ s, π ⁻¹ᵁ X.basicOpen r ≤ O) ∧
      ∀ x : X, x ∈ fullFiberInterior π O ↔ ∃ r ∈ s, x ∈ X.basicOpen r := by
  let _ := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have hfg := IsNoetherian.noetherian (denominatorIdeal π.appTop.hom O)
  obtain ⟨s, hs⟩ := hfg
  change Ideal.span (s : Set Γ(X, ⊤)) = denominatorIdeal π.appTop.hom O at hs
  refine ⟨s, hs, ?_, ?_, interior_iff_generator π O s hs⟩
  · rw [← X.zeroLocus_span (s : Set Γ(X, ⊤)), hs, zeroLocus_denominatorIdeal]
  · intro r hr
    have hd : r ∈ denominatorIdeal π.appTop.hom O := hs ▸ Ideal.subset_span hr
    exact (le_fullFiberInterior_iff π O _).mp
      ((basicOpen_le_fullFiberInterior_iff π O r).mpr hd)

end FLT.Mazur.SchemeOpenEnvelope
