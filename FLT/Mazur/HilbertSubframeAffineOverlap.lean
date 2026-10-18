/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeAffineTargets

/-!
# Actual common refinements of independent subframe chart pairs

Two independent source and target charts have simultaneous stable affine
refinements at every point where all selected images lie in both targets.
Both original source and target inclusions are retained for comparing actual
independent lifts, rather than only restrictions of a single chosen section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k

/-- Independently chosen source-target pairs have actual simultaneous affine overlaps. -/
theorem exists_normalized_subframe_affine_overlap (n : ℕ) (o : Fin n)
    (m : ℕ) (a : Fin m)
    (U₁ U₂ : (normalizedFullRelationFrames f hL d V c k n o).Opens)
    (h₁ : ∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U₁ = U₁)
    (h₂ : ∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U₂ = U₂)
    (T₁ T₂ : (normalizedFullRelationFrames f hL d V c k m a).Opens)
    (x : normalizedFullRelationFrames f hL d V c k n o) (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂)
    (ht₁ : ∀ ι : Fin m ↪ Fin n, subframeMap e o a ι x ∈ T₁)
    (ht₂ : ∀ ι : Fin m ↪ Fin n, subframeMap e o a ι x ∈ T₂) :
    ∃ T : (normalizedFullRelationFrames f hL d V c k m a).Opens,
      IsAffineOpen T ∧ T ≤ T₁ ∧ T ≤ T₂ ∧
      (∀ σ, (normalizedFullRelationAction f hL d V c k m a σ).hom ⁻¹ᵁ T = T) ∧
      ∃ Z : (normalizedFullRelationFrames f hL d V c k n o).Opens,
        IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U₁ ∧ Z ≤ U₂ ∧
        (∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ Z = Z) ∧
        ∀ ι : Fin m ↪ Fin n, Z ≤ subframeMap e o a ι ⁻¹ᵁ T := by
  obtain ⟨T, haT, hxT, hTT, hT⟩ :=
    exists_normalized_subframe_target_refinement f hL d V c k n o m a (T₁ ⊓ T₂) x
      (fun ι ↦ ⟨ht₁ ι, ht₂ ι⟩)
  have hU (σ : Equiv.Perm (Fin n)) :
      (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ (U₁ ⊓ U₂) = U₁ ⊓ U₂ := by
    rw [Scheme.Hom.preimage_inf, h₁, h₂]
  obtain ⟨Z, haZ, hxZ, hZU, _, hZ, hSel⟩ :=
    exists_normalized_finite_subframe_refinement f hL d V c k n o ⊤
      (by simp only [Scheme.Hom.preimage_top]) (U₁ ⊓ U₂) hU
      (fun _ : Unit ↦ m) (fun _ ↦ a) (fun _ ↦ T) x ⟨hx₁, hx₂⟩ (by trivial)
      (fun _ ↦ hxT)
  exact ⟨T, haT, hTT.trans inf_le_left, hTT.trans inf_le_right, hT,
    Z, haZ, hxZ, hZU.trans inf_le_left, hZU.trans inf_le_right, hZ, hSel ()⟩

end FLT.Mazur.HilbertChart.AffineRestriction
