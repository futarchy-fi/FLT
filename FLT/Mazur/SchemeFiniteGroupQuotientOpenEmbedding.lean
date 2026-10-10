/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotientMaps
public import FLT.Mazur.SchemeFiniteGroupQuotientOrbits

/-!
# Topological open embeddings between affine quotients

An equivariant open immersion between affine schemes induces an open embedding
on quotient spaces. The scheme open-immersion assertion still requires the
localization comparison on the structure sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X Y : Scheme.{u}}
variable (ρ : G →* Aut X) (τ : G →* Aut Y)
variable (f : X ⟶ Y) (hf : ∀ g : G, (ρ g).hom ≫ f = f ≫ (τ g).hom)

/-- Pointwise naturality of the quotient map. -/
lemma quotientHom_apply_quotientMap (x : X) :
    quotientHom ρ τ f hf (quotientMap ρ x) = quotientMap τ (f x) :=
  congrArg (fun k : X ⟶ quotient τ ↦ k x) (quotientMap_naturality ρ τ f hf)

variable [Finite G] [IsAffine X] [IsAffine Y]

/-- Equivariant point injections induce injections on affine quotients. -/
lemma quotientHom_injective (hi : Function.Injective f) :
    Function.Injective (quotientHom ρ τ f hf) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (quotientMap ρ).surjective a
  obtain ⟨y, rfl⟩ := (quotientMap ρ).surjective b
  rw [quotientHom_apply_quotientMap, quotientHom_apply_quotientMap] at hab
  obtain ⟨g, hg⟩ := (quotientMap_eq_iff_orbit τ (f x) (f y)).mp hab
  apply (quotientMap_eq_iff_orbit ρ x y).mpr
  refine ⟨g, hi ?_⟩
  exact hg.trans (congrArg (fun k : X ⟶ Y ↦ k x) (hf g)).symm

omit [IsAffine Y] in
/-- Images of opens under the quotient morphism can be computed before quotienting. -/
lemma quotientHom_image (V : Set (quotient ρ)) :
    quotientHom ρ τ f hf '' V = quotientMap τ '' (f '' (quotientMap ρ ⁻¹' V)) := by
  have he : quotientMap τ ∘ f = quotientHom ρ τ f hf ∘ quotientMap ρ := by
    funext x
    exact (quotientHom_apply_quotientMap ρ τ f hf x).symm
  simp only [Function.comp_def] at he
  calc
    quotientHom ρ τ f hf '' V =
        quotientHom ρ τ f hf '' (quotientMap ρ '' (quotientMap ρ ⁻¹' V)) := by
      rw [Set.image_preimage_eq _ (quotientMap ρ).surjective]
    _ = quotientMap τ '' (f '' (quotientMap ρ ⁻¹' V)) := by
      simp only [Set.image_image, he]

/-- Equivariant open immersions induce open maps of the quotient spaces. -/
lemma quotientHom_isOpenMap [IsOpenImmersion f] : IsOpenMap (quotientHom ρ τ f hf) := by
  intro V hV
  rw [quotientHom_image]
  apply quotientMap_image_isOpen τ _
    (f.isOpenEmbedding.isOpenMap _ (hV.preimage (quotientMap ρ).continuous))
  rintro g y ⟨x, hx, rfl⟩
  refine ⟨(ρ g).hom x, ?_, congrArg (fun k : X ⟶ Y ↦ k x) (hf g)⟩
  change quotientMap ρ ((ρ g).hom x) ∈ V
  have he := congrArg (fun k : X ⟶ quotient ρ ↦ k x) (quotientMap_invariant ρ g)
  exact he.symm ▸ hx

/-- The induced map is an open embedding on underlying spaces; no stalk claim is made. -/
lemma quotientHom_isOpenEmbedding [IsOpenImmersion f] :
    Topology.IsOpenEmbedding (quotientHom ρ τ f hf) :=
  .of_continuous_injective_isOpenMap (quotientHom ρ τ f hf).continuous
    (quotientHom_injective ρ τ f hf f.isOpenEmbedding.injective)
    (quotientHom_isOpenMap ρ τ f hf)

end FLT.Mazur.SchemeFiniteGroupQuotient
