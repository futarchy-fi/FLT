/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotientOpenImmersion
public import FLT.Mazur.FiniteGroupOpenRestriction

/-!
# The diagram of invariant affine quotient charts

Objects are actual stable affine opens of the original scheme. Arrows come
from inclusions, and the functor laws follow from scheme-level quotient
functoriality. All arrows are open immersions for a finite acting group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} (ρ : G →* Aut X)

/-- Actual invariant affine opens, ordered by inclusion. -/
abbrev Chart := {U : X.Opens // IsAffineOpen U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U}

/-- Each object of the chart diagram is affine as a scheme. -/
instance chart_isAffine (U : Chart ρ) : IsAffine U.val.toScheme := U.property.1

/-- The actual restricted action on a stable affine chart. -/
def action (U : Chart ρ) : G →* Aut U.val.toScheme :=
  FiniteGroupRestriction.restrictedAction ρ U.val U.property.2

/-- Chart inclusions are equivariant for the restricted actions. -/
@[reassoc]
lemma inclusion_equivariant {U V : Chart ρ} (h : U ≤ V) (g : G) :
    (action ρ U g).hom ≫ X.homOfLE h = X.homOfLE h ≫ (action ρ V g).hom :=
  (FiniteGroupRestriction.inclusion_equivariant ρ V.val V.property.2
    U.val U.property.2 h g).symm

/-- Quotient inclusions associated to inclusions of actual affine opens. -/
def inclusion {U V : Chart ρ} (h : U ≤ V) : quotient (action ρ U) ⟶ quotient (action ρ V) :=
  quotientHom (action ρ U) (action ρ V) (X.homOfLE h) (inclusion_equivariant ρ h)

/-- Quotient inclusions preserve identities. -/
@[simp]
lemma inclusion_refl (U : Chart ρ) : inclusion ρ (le_refl U) = 𝟙 _ := by
  unfold inclusion
  have he : X.homOfLE (show U.val ≤ U.val from le_refl U) = 𝟙 U.val.toScheme := by
    rw [← cancel_mono U.val.ι, Scheme.homOfLE_ι, Category.id_comp]
  simp only [he, quotientHom_id]

/-- Quotient inclusions preserve composition. -/
@[reassoc]
lemma inclusion_trans {U V W : Chart ρ} (h : U ≤ V) (k : V ≤ W) :
    inclusion ρ h ≫ inclusion ρ k = inclusion ρ (h.trans k) := by
  unfold inclusion
  rw [quotientHom_comp _ _ _ _ _ _ _ (fun g ↦ by
    rw [inclusion_equivariant_assoc, inclusion_equivariant, Category.assoc])]
  simp only [Scheme.homOfLE_homOfLE]

/-- The actual functor of affine quotient schemes. -/
def diagram : Chart ρ ⥤ Scheme.{u} where
  obj U := quotient (action ρ U)
  map h := inclusion ρ (leOfHom h)
  map_id U := inclusion_refl ρ U
  map_comp h k := (inclusion_trans ρ (leOfHom h) (leOfHom k)).symm

/-- Every arrow of the quotient diagram is an open immersion. -/
instance inclusion_isOpenImmersion [Finite G] {U V : Chart ρ} (h : U ≤ V) :
    IsOpenImmersion (inclusion ρ h) := by
  unfold inclusion
  infer_instance

/-- The diagram has open-immersion transition morphisms. -/
instance diagram_map_isOpenImmersion [Finite G] {U V : Chart ρ} (h : U ⟶ V) :
    IsOpenImmersion ((diagram ρ).map h) := inclusion_isOpenImmersion ρ (leOfHom h)

/-- Quotient inclusions commute with the original chart quotient maps. -/
@[reassoc]
lemma quotient_inclusion {U V : Chart ρ} (h : U ≤ V) :
    quotientMap (action ρ U) ≫ inclusion ρ h = X.homOfLE h ≫ quotientMap (action ρ V) :=
  quotientMap_naturality _ _ _ _

end FLT.Mazur.StableAffineQuotient
