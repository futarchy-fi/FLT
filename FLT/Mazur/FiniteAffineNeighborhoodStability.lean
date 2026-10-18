/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Finite affine neighborhoods under the atlas constructions

The property that every finite set lies in an affine open is preserved by
closed embeddings, open restriction, and products over an affine base. This
constructs neighborhoods for marking loci without assuming an ample line there.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Every finite set of points lies in one actual affine open. -/
def HasNeighborhoods (X : Scheme) : Prop :=
  ∀ (s : Set X), s.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U

/-- An affine scheme has the finite-neighborhood property. -/
theorem of_affine (X : Scheme) [IsAffine X] : HasNeighborhoods X :=
  fun _ _ => ⟨⊤, isAffineOpen_top X, Set.subset_univ _⟩

/-- Pullback along an affine morphism preserves common affine neighborhoods. -/
theorem of_affineHom {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f]
    (hY : HasNeighborhoods Y) : HasNeighborhoods X := by
  intro s hs
  obtain ⟨U, hU, hsU⟩ := hY (f '' s) (hs.image f)
  exact ⟨f ⁻¹ᵁ U, hU.preimage f, fun x hx => hsU (Set.mem_image_of_mem f hx)⟩

/-- Prime avoidance refines a common affine neighborhood inside any prescribed open. -/
theorem within {X : Scheme} (hX : HasNeighborhoods X) (W : X.Opens)
    (s : Set X) (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W := by
  obtain ⟨V, hV, hsV⟩ := hX s hs
  let _ : IsAffine V.toScheme := hV
  let t : Set V.toScheme := V.ι ⁻¹' s
  have ht : t.Finite := hs.preimage Subtype.val_injective.injOn
  obtain ⟨a, ha, haW⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (V.ι ⁻¹ᵁ W) t ht (fun _ hx => hsW hx)
  refine ⟨V.ι ''ᵁ V.toScheme.basicOpen a,
    ((isAffineOpen_top V.toScheme).basicOpen a).image_of_isOpenImmersion V.ι, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hsV hx⟩, ha hx, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    exact haW hy

/-- Open subschemes retain finite affine neighborhoods. -/
theorem of_openImmersion {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
    (hY : HasNeighborhoods Y) : HasNeighborhoods X := by
  intro s hs
  obtain ⟨U, hU, hsU, hUW⟩ := within hY (j ''ᵁ ⊤) (j '' s) (hs.image j)
    (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, trivial, rfl⟩)
  refine ⟨j ⁻¹ᵁ U, hU.preimage_of_isOpenImmersion j ?_, ?_⟩
  · exact hUW.trans (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩)
  · exact fun x hx => hsU (Set.mem_image_of_mem j hx)

/-- Two affine neighborhoods give an affine neighborhood in a relative product. -/
theorem pullback {X Y S : Scheme} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (hX : HasNeighborhoods X) (hY : HasNeighborhoods Y) :
    HasNeighborhoods (Limits.pullback f g) := by
  intro s hs
  obtain ⟨U, hU, hsU⟩ := hX (pullback.fst f g '' s) (hs.image _)
  obtain ⟨V, hV, hsV⟩ := hY (pullback.snd f g '' s) (hs.image _)
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine V.toScheme := hV
  let p : Limits.pullback (U.ι ≫ f) (V.ι ≫ g) ⟶ Limits.pullback f g :=
    pullback.map _ _ _ _ U.ι V.ι (𝟙 S) (by simp) (by simp)
  have hp : IsOpenImmersion p := by dsimp [p]; infer_instance
  refine ⟨p.opensRange, isAffineOpen_opensRange p, ?_⟩
  intro x hx
  change x ∈ Set.range p
  simpa only [p, Scheme.Pullback.range_map, Scheme.Opens.range_ι,
    Set.mem_inter_iff, Set.mem_preimage] using
    And.intro (hsU (Set.mem_image_of_mem _ hx)) (hsV (Set.mem_image_of_mem _ hx))

/-- The actual binary product in the over category retains finite neighborhoods. -/
theorem overProd {S : Scheme} [IsAffine S] (X Y : Over S)
    (hX : HasNeighborhoods X.left) (hY : HasNeighborhoods Y.left) :
    HasNeighborhoods (X ⨯ Y).left :=
  of_affineHom (Over.prodLeftIsoPullback X Y).hom (pullback X.hom Y.hom hX hY)

end FLT.Mazur.FiniteAffineNeighborhood
