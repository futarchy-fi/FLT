/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientMap
public import FLT.Mazur.SchemeFiniteGroupAffineDescent

/-!
# Affine-target descent through the glued quotient

The uniquely descended affine chart maps form an actual cocone on the
quotient diagram. Its universal property constructs and uniquely determines
the global descended morphism to an arbitrary affine target scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] {X Y : Scheme.{u}}
variable [IsAffine Y] (ρ : G →* Aut X) (f : X ⟶ Y)
variable (hf : ∀ g : G, (ρ g).hom ≫ f = f)

include hf in
omit [IsAffine Y] in
/-- An invariant global morphism restricts to an invariant morphism on every chart. -/
lemma chart_invariant (U : Chart ρ) (g : G) :
    (action ρ U g).hom ≫ (U.val.ι ≫ f) = U.val.ι ≫ f := by
  unfold action
  rw [FiniteGroupRestriction.restrictedAction_hom_ι_assoc, hf]

/-- The uniquely constructed affine-target descent on an actual quotient chart. -/
def affineLocalDesc (U : Chart ρ) : quotient (action ρ U) ⟶ Y :=
  (existsUnique_affine_desc (action ρ U) (U.val.ι ≫ f) (chart_invariant ρ f hf U)).choose

/-- The descended chart morphism factors the original map. -/
@[reassoc]
lemma affineLocalDesc_fac (U : Chart ρ) :
    quotientMap (action ρ U) ≫ affineLocalDesc ρ f hf U = U.val.ι ≫ f :=
  (existsUnique_affine_desc (action ρ U) (U.val.ι ≫ f)
    (chart_invariant ρ f hf U)).choose_spec.1

/-- Uniqueness on each affine chart determines every compatible factorization. -/
lemma affineLocalDesc_unique (U : Chart ρ) (k : quotient (action ρ U) ⟶ Y)
    (hk : quotientMap (action ρ U) ≫ k = U.val.ι ≫ f) : k = affineLocalDesc ρ f hf U :=
  (existsUnique_affine_desc (action ρ U) (U.val.ι ≫ f)
    (chart_invariant ρ f hf U)).choose_spec.2 k hk

/-- Unique affine descents agree under all inclusions of invariant charts. -/
@[reassoc]
lemma inclusion_affineLocalDesc {U V : Chart ρ} (h : U ≤ V) :
    inclusion ρ h ≫ affineLocalDesc ρ f hf V = affineLocalDesc ρ f hf U := by
  apply affineLocalDesc_unique
  rw [quotient_inclusion_assoc, affineLocalDesc_fac, Scheme.homOfLE_ι_assoc]

/-- The descended maps form a cocone on the actual quotient diagram. -/
def affineDescCocone : Cocone (diagram ρ) where
  pt := Y
  ι.app U := affineLocalDesc ρ f hf U
  ι.naturality {U V} h := by
    change inclusion ρ (leOfHom h) ≫ affineLocalDesc ρ f hf V =
      affineLocalDesc ρ f hf U ≫ 𝟙 Y
    rw [Category.comp_id]
    exact inclusion_affineLocalDesc ρ f hf (leOfHom h)

variable [Finite G] [X.IsSeparated]

/-- The descended global morphism from the constructed glued quotient. -/
def affineDesc : glued ρ ⟶ Y := colimit.desc (diagram ρ) (affineDescCocone ρ f hf)

/-- The global descent has the prescribed affine restriction on every quotient chart. -/
@[reassoc]
lemma chartMap_affineDesc (U : Chart ρ) :
    chartMap ρ U ≫ affineDesc ρ f hf = affineLocalDesc ρ f hf U :=
  colimit.ι_desc (affineDescCocone ρ f hf) U

variable (hcover : ⨆ U : Chart ρ, U.val = ⊤)

/-- The descended morphism factors the original invariant global morphism. -/
@[reassoc]
lemma affineDesc_fac : map ρ hcover ≫ affineDesc ρ f hf = f := by
  apply (sourceCover ρ hcover).hom_ext
  intro U
  change U.val.ι ≫ map ρ hcover ≫ affineDesc ρ f hf = U.val.ι ≫ f
  rw [ι_map_assoc]
  change (quotientMap (action ρ U) ≫ chartMap ρ U) ≫ affineDesc ρ f hf = _
  rw [Category.assoc, chartMap_affineDesc, affineLocalDesc_fac]

include hf in
/-- Every invariant morphism to an affine scheme descends uniquely through the glued quotient. -/
theorem existsUnique_affineDesc : ∃! h : glued ρ ⟶ Y, map ρ hcover ≫ h = f := by
  refine ⟨affineDesc ρ f hf, affineDesc_fac ρ f hf hcover, ?_⟩
  intro k hk
  apply colimit.hom_ext
  intro U
  change chartMap ρ U ≫ k = chartMap ρ U ≫ affineDesc ρ f hf
  rw [chartMap_affineDesc]
  apply affineLocalDesc_unique
  rw [← Category.assoc]
  change localMap ρ U ≫ k = _
  rw [← ι_map ρ hcover U, Category.assoc, hk]

end FLT.Mazur.StableAffineQuotient
