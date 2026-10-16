/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedStableAffine
public import FLT.Mazur.FiniteGroupClosedEnvelopeRefinement
public import FLT.Mazur.EquivalenceRelationNormalizedInvariantOpen

/-!
# Moving affine source charts inside original invariant domains

The actual normalized Hilbert charts refine every stable source open. Thus
their overlaps and the inverse images of original invariant domains have
stable affine charts, for every frame size and distinguished label.
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
  (n : ℕ) (o : Fin n)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedFullRelationAction f hL d V c k n o
local notation "π" => normalizedFullRelationFirst f hL d V c k n o

/-- Stable affine source charts refine every stable open around each of its points. -/
theorem exists_normalized_affine_refinement (W : (N).Opens)
    (hW : ∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ W = W) (x : N) (hx : x ∈ W) :
    ∃ U : (N).Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      (∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ U = U) ∧ Etale (U.ι ≫ π) := by
  let _ := RelativeOrderedTuples.finTuples_affine (firstRelationEnvelope (A := A) V) n
  obtain ⟨U, ha, hxU, hUW, hU⟩ :=
    FiniteGroupNeighborhood.exists_closed_envelope_affine_basis ρ
      (normalizedOriginalFrameInclusion f hL d V c k n o)
      (fullRelationOrderedEnvelopeMap f hL d V c k n) W hW x hx
  exact ⟨U, ha, hxU, hUW, hU, inferInstance⟩

/-- Two moving source charts have actual affine common refinements at every overlap point. -/
theorem exists_normalized_affine_overlap (U₁ U₂ : (N).Opens)
    (h₁ : ∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ U₁ = U₁)
    (h₂ : ∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ U₂ = U₂)
    (x : N) (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) :
    ∃ U : (N).Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ U₁ ∧ U ≤ U₂ ∧
      (∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ U = U) ∧ Etale (U.ι ≫ π) := by
  obtain ⟨U, ha, hx, hU, he, het⟩ :=
    exists_normalized_affine_refinement f hL d V c k n o (U₁ ⊓ U₂)
      (fun σ ↦ by simp only [Scheme.Hom.preimage_inf, h₁ σ, h₂ σ]) x ⟨hx₁, hx₂⟩
  exact ⟨U, ha, hx, hU.trans inf_le_left, hU.trans inf_le_right, he, het⟩

/-- An original invariant domain has affine moving charts wholly inside its inverse image. -/
theorem exists_normalized_affine_original_domain (W : A.left.Opens)
    (hW : (p) ⁻¹ᵁ W = (q) ⁻¹ᵁ W) (x : N) (hx : π x ∈ W) :
    ∃ U : (N).Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ π ⁻¹ᵁ W ∧
      (∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ U = U) ∧ Etale (U.ι ≫ π) :=
  exists_normalized_affine_refinement f hL d V c k n o (π ⁻¹ᵁ W)
    (first_preimage_stable (fullRelationSchemeEquivalence f hL d V c k) (Fin n) o W hW) x hx

end FLT.Mazur.HilbertChart.AffineRestriction
