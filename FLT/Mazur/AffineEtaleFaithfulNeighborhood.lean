/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Faithful principal neighborhoods of an original affine étale morphism

The base open is constructed inside the actual image. Restricting the original
morphism to this open is surjective; no global surjectivity is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleFaithfulNeighborhood
variable {V S : Scheme.{0}} (g : V ⟶ S) [IsAffine S] [Etale g]

/-- Each original point admits a principal base neighborhood inside the actual image. -/
theorem exists_principal_image_neighborhood (x : V) :
    ∃ r : Γ(S, ⊤), g x ∈ S.basicOpen r ∧
      (S.basicOpen r : Set S) ⊆ Set.range g := by
  let U : S.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  obtain ⟨r, hr, hxr⟩ := (isAffineOpen_top S).exists_basicOpen_le
    (⟨g x, ⟨x, rfl⟩⟩ : U) (show g x ∈ (⊤ : S.Opens) from trivial)
  exact ⟨r, hxr, hr⟩

/-- The selected function lies in the original base coefficient ring. -/
def parameter (x : V) : Γ(S, ⊤) :=
  (exists_principal_image_neighborhood g x).choose

/-- The constructed principal open in the original base. -/
def baseOpen (x : V) : S.Opens := S.basicOpen (parameter g x)

/-- The original point survives the chosen localization. -/
theorem mem_baseOpen (x : V) : g x ∈ baseOpen g x :=
  (exists_principal_image_neighborhood g x).choose_spec.1

/-- Every point of the constructed base open has an original preimage. -/
theorem baseOpen_le_range (x : V) : (baseOpen g x : Set S) ⊆ Set.range g :=
  (exists_principal_image_neighborhood g x).choose_spec.2

/-- The new source is the full inverse image, with all original points retained. -/
def sourceOpen (x : V) : V.Opens := g ⁻¹ᵁ baseOpen g x

/-- The restricted morphism is the original map on the full inverse image. -/
def map (x : V) : (sourceOpen g x).toScheme ⟶ (baseOpen g x).toScheme :=
  g ∣_ baseOpen g x

/-- The actual original structural square commutes. -/
@[reassoc]
theorem map_ι (x : V) : map g x ≫ (baseOpen g x).ι = (sourceOpen g x).ι ≫ g :=
  morphismRestrict_ι g (baseOpen g x)

/-- This is the full base change of the original translation morphism. -/
theorem isPullback (x : V) :
    IsPullback (sourceOpen g x).ι (map g x) g (baseOpen g x).ι :=
  (isPullback_morphismRestrict g (baseOpen g x)).flip

instance base_affine (x : V) : IsAffine (baseOpen g x).toScheme :=
  (isAffineOpen_top S).basicOpen _

instance source_affine [IsAffine V] (x : V) : IsAffine (sourceOpen g x).toScheme := by
  change IsAffine (g ⁻¹ᵁ S.basicOpen (parameter g x)).toScheme
  rw [Scheme.Hom.preimage_basicOpen_top]
  exact (isAffineOpen_top V).basicOpen _

instance map_etale (x : V) : Etale (map g x) :=
  MorphismProperty.of_isPullback (isPullback g x) (inferInstanceAs (Etale g))

/-- Faithful coverage is proved from image containment, not added as a hypothesis. -/
instance map_surjective (x : V) : Surjective (map g x) := by
  constructor
  intro y
  obtain ⟨z, hz⟩ := baseOpen_le_range g x y.property
  refine ⟨⟨z, show g z ∈ baseOpen g x from hz ▸ y.property⟩, ?_⟩
  apply (baseOpen g x).ι.isOpenEmbedding.injective
  change (map g x ≫ (baseOpen g x).ι) _ = _
  rw [map_ι]
  exact hz

end FLT.Mazur.AffineEtaleFaithfulNeighborhood
