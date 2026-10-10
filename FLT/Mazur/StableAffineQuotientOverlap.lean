/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientDiagram
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Intersections and local directedness of affine quotient charts

Intersecting actual invariant affine opens supplies all overlap charts.
The orbit-fiber theorem proves that any pair of quotient points identified
in a larger chart already comes from their intersection. This is the
pointwise hypothesis of scheme gluing, proved here from the original action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} (ρ : G →* Aut X)

/-- The restricted action is the original action on underlying chart points. -/
lemma action_apply (U : Chart ρ) (g : G) (x : U.val.toScheme) :
    ((action ρ U g).hom x).val = (ρ g).hom x.val :=
  congrArg (fun f : U.val.toScheme ⟶ X ↦ f x)
    (FiniteGroupRestriction.restrictedAction_hom_ι ρ U.val U.property.2 g)

/-- Pointwise naturality for the actual quotient inclusions. -/
lemma inclusion_apply_quotientMap {U V : Chart ρ} (h : U ≤ V) (x : U.val.toScheme) :
    inclusion ρ h (quotientMap (action ρ U) x) =
      quotientMap (action ρ V) (X.homOfLE h x) :=
  congrArg (fun f : U.val.toScheme ⟶ quotient (action ρ V) ↦ f x)
    (quotient_inclusion ρ h)

variable [X.IsSeparated]

/-- The intersection of invariant affine charts remains an invariant affine chart. -/
def intersection (U V : Chart ρ) : Chart ρ :=
  ⟨U.val ⊓ V.val, U.property.1.inf V.property.1, fun g ↦ by
    change (ρ g).hom ⁻¹ᵁ U.val ⊓ (ρ g).hom ⁻¹ᵁ V.val = _
    rw [U.property.2, V.property.2]⟩

/-- Intersected charts include into the first factor. -/
lemma intersection_le_left (U V : Chart ρ) : intersection ρ U V ≤ U :=
  show U.val ⊓ V.val ≤ U.val from inf_le_left

/-- Intersected charts include into the second factor. -/
lemma intersection_le_right (U V : Chart ρ) : intersection ρ U V ≤ V :=
  show U.val ⊓ V.val ≤ V.val from inf_le_right

variable [Finite G]

omit [X.IsSeparated] in
/-- Equal quotient points in a larger chart have a representative in the intersection. -/
theorem exists_intersection_representative {U V W : Chart ρ} (hU : U ≤ W) (hV : V ≤ W)
    (a : U.val.toScheme) (b : V.val.toScheme)
    (hab : inclusion ρ hU (quotientMap (action ρ U) a) =
      inclusion ρ hV (quotientMap (action ρ V) b)) : a.val ∈ V.val := by
  rw [inclusion_apply_quotientMap, inclusion_apply_quotientMap] at hab
  obtain ⟨g, hg⟩ := (quotientMap_eq_iff_orbit (action ρ W) _ _).mp hab
  have he : b.val = (ρ g).hom a.val := by
    have ht := congrArg (fun x : W.val.toScheme ↦ x.val) hg
    simpa only [action_apply, Scheme.homOfLE_apply] using ht
  rw [← V.property.2 g]
  change (ρ g).hom a.val ∈ V.val
  rw [← he]
  exact b.property

/-- The actual quotient diagram satisfies the gluing condition on pointwise overlaps. -/
instance diagram_isLocallyDirected : (diagram ρ ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro U V W hU hV z w hzw
  change inclusion ρ (leOfHom hU) z = inclusion ρ (leOfHom hV) w at hzw
  obtain ⟨a, rfl⟩ := (quotientMap (action ρ U)).surjective z
  obtain ⟨b, rfl⟩ := (quotientMap (action ρ V)).surjective w
  have ha := exists_intersection_representative ρ (leOfHom hU) (leOfHom hV) a b hzw
  let T := intersection ρ U V
  let t : T.val.toScheme := ⟨a.val, a.property, ha⟩
  have ht : inclusion ρ (intersection_le_left ρ U V) (quotientMap (action ρ T) t) =
      quotientMap (action ρ U) a := by
    rw [inclusion_apply_quotientMap]
    apply congrArg (quotientMap (action ρ U))
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _
  refine ⟨T, homOfLE (intersection_le_left ρ U V),
    homOfLE (intersection_le_right ρ U V), quotientMap (action ρ T) t, ht, ?_⟩
  apply (inclusion ρ (leOfHom hV)).isOpenEmbedding.injective
  change (inclusion ρ (intersection_le_right ρ U V) ≫ inclusion ρ (leOfHom hV)) _ = _
  rw [inclusion_trans]
  have hc : inclusion ρ ((intersection_le_right ρ U V).trans (leOfHom hV)) =
      inclusion ρ (intersection_le_left ρ U V) ≫ inclusion ρ (leOfHom hU) :=
    (inclusion_trans ρ _ _).symm
  rw [hc, Scheme.Hom.comp_apply, ht]
  exact hzw

end FLT.Mazur.StableAffineQuotient
