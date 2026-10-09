/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientGluing

/-!
# The map to the glued finite-group quotient

When invariant affine opens cover the original scheme, their quotient maps
agree on actual scheme intersections and glue to a global invariant,
surjective morphism. The coverage hypothesis will be supplied by ampleness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X)

/-- The original chart maps into its quotient and then into the glued scheme. -/
def localMap (U : Chart ρ) : U.val.toScheme ⟶ glued ρ :=
  quotientMap (action ρ U) ≫ chartMap ρ U

/-- The original chart maps agree along inclusions of actual opens. -/
@[reassoc]
lemma inclusion_localMap {U V : Chart ρ} (h : U ≤ V) :
    X.homOfLE h ≫ localMap ρ V = localMap ρ U := by
  unfold localMap
  rw [← quotient_inclusion_assoc, inclusion_chartMap]

/-- Compatibility holds on the scheme pullback of each pair of original charts. -/
lemma localMap_compatible (U V : Chart ρ) :
    pullback.fst U.val.ι V.val.ι ≫ localMap ρ U =
      pullback.snd U.val.ι V.val.ι ≫ localMap ρ V := by
  let e := (isPullback_opens_inf U.val V.val).isoPullback
  rw [← cancel_epi e.hom]
  simp only [e, ← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  exact (inclusion_localMap ρ (intersection_le_left ρ U V)).trans
    (inclusion_localMap ρ (intersection_le_right ρ U V)).symm

variable (hcover : ⨆ U : Chart ρ, U.val = ⊤)

/-- The actual open cover of the original scheme by all invariant affine charts. -/
def sourceCover : X.OpenCover := X.openCoverOfIsOpenCover (fun U : Chart ρ ↦ U.val) hcover

/-- The global quotient morphism, glued from the actual affine quotient maps. -/
def map : X ⟶ glued ρ :=
  (sourceCover ρ hcover).glueMorphisms (localMap ρ) (localMap_compatible ρ)

/-- The constructed global map restricts to the prescribed affine quotient on every chart. -/
@[reassoc]
lemma ι_map (U : Chart ρ) : U.val.ι ≫ map ρ hcover = localMap ρ U :=
  (sourceCover ρ hcover).ι_glueMorphisms _ _ U

/-- The constructed global map is invariant under the original scheme action. -/
@[reassoc]
lemma map_invariant (g : G) : (ρ g).hom ≫ map ρ hcover = map ρ hcover := by
  apply (sourceCover ρ hcover).hom_ext
  intro U
  change U.val.ι ≫ (ρ g).hom ≫ map ρ hcover = U.val.ι ≫ map ρ hcover
  rw [← FiniteGroupRestriction.restrictedAction_hom_ι_assoc ρ U.val U.property.2,
    ι_map]
  change (action ρ U g).hom ≫ localMap ρ U = localMap ρ U
  unfold localMap
  rw [quotientMap_invariant_assoc]

/-- Every point of the glued scheme comes from the original scheme. -/
theorem map_surjective : Function.Surjective (map ρ hcover) := by
  intro z
  obtain ⟨U, q, rfl⟩ := exists_chartMap ρ z
  obtain ⟨x, rfl⟩ := (quotientMap (action ρ U)).surjective q
  refine ⟨x.val, ?_⟩
  exact congrArg (fun f : U.val.toScheme ⟶ glued ρ ↦ f x) (ι_map ρ hcover U)

end FLT.Mazur.StableAffineQuotient
