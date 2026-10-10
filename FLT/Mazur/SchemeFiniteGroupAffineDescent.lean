/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotient

/-!
# Descent to affine targets for actual scheme actions

Transport the invariant-ring universal property along the canonical affine
scheme isomorphisms. The resulting factorization and its uniqueness refer
to the actual source, target, action, and quotient morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
variable (ρ : G →* Aut X) (f : X ⟶ Y)
variable (hf : ∀ g : G, (ρ g).hom ≫ f = f)

include hf in
/-- Every invariant map between actual affine schemes factors uniquely through the quotient. -/
theorem existsUnique_affine_desc :
    ∃! h : quotient ρ ⟶ Y, quotientMap ρ ≫ h = f := by
  let _ := coordinateAction ρ
  have ht (g : G) :
      FiniteGroupQuotient.actionMap G Γ(X, ⊤) g ≫ X.isoSpec.inv =
        X.isoSpec.inv ≫ (ρ g⁻¹).hom := by
    rw [← cancel_mono X.toSpecΓ]
    simp only [Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
    rw [toSpecΓ_equivariant, Scheme.isoSpec_inv_toSpecΓ_assoc, inv_inv]
    change Spec.map (CommRingCat.ofHom (coordinateHom ρ g)) ≫ 𝟙 _ = _
    exact Category.comp_id _
  obtain ⟨h, hh, hu⟩ := FiniteGroupQuotient.existsUnique_affine_desc G Γ(X, ⊤) Γ(Y, ⊤)
    (X.isoSpec.inv ≫ f ≫ Y.toSpecΓ) (fun g ↦ by
      rw [← Category.assoc, ht g, Category.assoc, ← Category.assoc (ρ g⁻¹).hom, hf])
  refine ⟨h ≫ Y.isoSpec.inv, ?_, ?_⟩
  · change (X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤)) ≫ _ = _
    rw [Category.assoc, ← Category.assoc (FiniteGroupQuotient.quotientMap G Γ(X, ⊤)),
      hh]
    simp only [Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id,
      Scheme.toSpecΓ_isoSpec_inv_assoc]
  · intro k hk
    rw [← cancel_mono Y.toSpecΓ]
    simp only [Category.assoc, Scheme.isoSpec_inv_toSpecΓ, Category.comp_id]
    apply hu
    rw [← cancel_epi X.toSpecΓ]
    change quotientMap ρ ≫ k ≫ Y.toSpecΓ = X.toSpecΓ ≫ X.isoSpec.inv ≫ f ≫ Y.toSpecΓ
    rw [← Category.assoc, hk, Scheme.toSpecΓ_isoSpec_inv_assoc]

end FLT.Mazur.SchemeFiniteGroupQuotient
