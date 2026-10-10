/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotientMaps

/-!
# Equivariant isomorphisms induce quotient isomorphisms

The inverse is constructed from the inverse scheme map and functoriality.
No assumption about the quotient structure sheaf is required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X Y : Scheme.{u}}
variable (ρ : G →* Aut X) (τ : G →* Aut Y)

/-- The quotient map associated to an identity is the identity. -/
@[simp]
lemma quotientHom_id (h : ∀ g : G, (ρ g).hom ≫ 𝟙 X = 𝟙 X ≫ (ρ g).hom) :
    quotientHom ρ ρ (𝟙 X) h = 𝟙 (quotient ρ) := by
  unfold quotientHom
  have he : CommRingCat.ofHom (invariantMap ρ ρ (𝟙 X) h) =
      𝟙 (CommRingCat.of (invariantCoordinates ρ)) := by
    ext a
    rfl
  rw [he, Spec.map_id]
  rfl

/-- The inverse of an equivariant isomorphism is equivariant. -/
lemma inverse_equivariant (e : X ≅ Y)
    (he : ∀ g : G, (ρ g).hom ≫ e.hom = e.hom ≫ (τ g).hom) (g : G) :
    (τ g).hom ≫ e.inv = e.inv ≫ (ρ g).hom := by
  rw [← cancel_mono e.hom]
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [he g, e.inv_hom_id_assoc]

/-- The actual isomorphism of spectra induced by an equivariant scheme isomorphism. -/
def quotientIso (e : X ≅ Y)
    (he : ∀ g : G, (ρ g).hom ≫ e.hom = e.hom ≫ (τ g).hom) :
    quotient ρ ≅ quotient τ where
  hom := quotientHom ρ τ e.hom he
  inv := quotientHom τ ρ e.inv (inverse_equivariant ρ τ e he)
  hom_inv_id := by
    rw [quotientHom_comp ρ τ e.hom he ρ e.inv (inverse_equivariant ρ τ e he)
      (fun g ↦ by simp)]
    simpa only [e.hom_inv_id] using quotientHom_id ρ (fun g ↦ by simp)
  inv_hom_id := by
    rw [quotientHom_comp τ ρ e.inv (inverse_equivariant ρ τ e he) τ e.hom he
      (fun g ↦ by simp)]
    simpa only [e.inv_hom_id] using quotientHom_id τ (fun g ↦ by simp)

/-- Any equivariant isomorphism gives an isomorphism on fixed-coordinate quotients. -/
instance quotientHom_isIso (f : X ⟶ Y) [IsIso f]
    (hf : ∀ g : G, (ρ g).hom ≫ f = f ≫ (τ g).hom) :
    IsIso (quotientHom ρ τ f hf) :=
  (quotientIso ρ τ (asIso f) hf).isIso_hom

end FLT.Mazur.SchemeFiniteGroupQuotient
