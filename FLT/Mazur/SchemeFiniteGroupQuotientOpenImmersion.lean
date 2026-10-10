/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupPrincipalComparison
public import FLT.Mazur.SchemeFiniteGroupQuotientOpenEmbedding
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open immersions on finite-group quotients

Invariant principal opens inside the image provide a source cover. On every
member the quotient map is a composite of the proved principal-chart
isomorphism and the invariant-localization open immersion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X Y : Scheme.{u}}
variable [IsAffine X] [IsAffine Y]
variable (ρ : G →* Aut X) (τ : G →* Aut Y)
variable (f : X ⟶ Y) [IsOpenImmersion f]
variable (hf : ∀ g : G, (ρ g).hom ≫ f = f ≫ (τ g).hom)

include hf

omit [Finite G] [IsAffine X] [IsAffine Y] in
/-- The image of an equivariant morphism is stable under the target action. -/
lemma equivariant_range_stable (g : G) (y : Y) (hy : y ∈ f.opensRange) :
    (τ g).hom y ∈ f.opensRange := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨(ρ g).hom x, congrArg (fun k : X ⟶ Y ↦ k x) (hf g)⟩

/-- An equivariant affine open immersion induces an open immersion of quotient schemes. -/
instance quotientHom_isOpenImmersion : IsOpenImmersion (quotientHom ρ τ f hf) := by
  apply IsOpenImmersion.of_forall_source_exists _
    (quotientHom_injective ρ τ f hf f.isOpenEmbedding.injective)
  intro z
  obtain ⟨x, rfl⟩ := (quotientMap ρ).surjective z
  obtain ⟨r, hrx, hr⟩ := exists_invariant_principal τ f.opensRange
    (equivariant_range_stable ρ τ f hf) (f x) ⟨x, rfl⟩
  let s := invariantMap ρ τ f hf r
  refine ⟨quotient (principalAction ρ s), principalQuotientMap ρ s, inferInstance, ?_, ?_⟩
  · rw [principalQuotientMap_opensRange]
    change x ∈ quotientMap ρ ⁻¹ᵁ PrimeSpectrum.basicOpen s
    rw [quotientMap_preimage_basicOpen]
    change x ∈ X.basicOpen (f.appTop.hom (r : Γ(Y, ⊤)))
    rw [← Scheme.preimage_basicOpen_top]
    exact hrx
  · rw [← principalQuotientIso_hom_map ρ τ f hf r hr]
    infer_instance

end FLT.Mazur.SchemeFiniteGroupQuotient
