/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupPullbackAction

/-!
# Equivariant comparisons with actual pullbacks

A cartesian model with equivariant first projection and invariant second
projection has the actual pullback action. These are equalities of scheme
morphisms, so the comparisons preserve the structure sheaves as well as points.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupPullback

universe u
variable {G : Type*} [Group G] {X Q S P : Scheme.{u}}
variable (ρ : G →* Aut X) (q : X ⟶ Q) (hq : ∀ g : G, (ρ g).hom ≫ q = q)
variable (f : S ⟶ Q) {a : P ⟶ X} {b : P ⟶ S} (h : IsPullback a b q f)

/-- Equivariance of a cartesian model follows from its two actual projections. -/
@[reassoc]
lemma isoPullback_equivariant (g : G) (t : P ⟶ P)
    (ha : t ≫ a = a ≫ (ρ g).hom) (hb : t ≫ b = b) :
    t ≫ h.isoPullback.hom = h.isoPullback.hom ≫ (action ρ q hq f g).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, h.isoPullback_hom_fst, Category.assoc, action_fst,
      h.isoPullback_hom_fst_assoc, ha]
  · rw [Category.assoc, h.isoPullback_hom_snd, Category.assoc, action_snd,
      h.isoPullback_hom_snd, hb]

/-- The inverse comparison also intertwines the scheme endomorphisms. -/
@[reassoc]
lemma isoPullback_inv_equivariant (g : G) (t : P ⟶ P)
    (ha : t ≫ a = a ≫ (ρ g).hom) (hb : t ≫ b = b) :
    (action ρ q hq f g).hom ≫ h.isoPullback.inv = h.isoPullback.inv ≫ t := by
  rw [← cancel_mono h.isoPullback.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [isoPullback_equivariant ρ q hq f h g t ha hb, Iso.inv_hom_id_assoc]

/-- Invariance transfers across a cartesian action comparison in both directions. -/
lemma invariant_iff_model (τ : G →* Aut P)
    (ha : ∀ g, (τ g).hom ≫ a = a ≫ (ρ g).hom)
    (hb : ∀ g, (τ g).hom ≫ b = b) {Y : Scheme.{u}}
    (k : pullback q f ⟶ Y) :
    (∀ g, (action ρ q hq f g).hom ≫ k = k) ↔
      ∀ g, (τ g).hom ≫ h.isoPullback.hom ≫ k = h.isoPullback.hom ≫ k := by
  constructor
  · intro hk g
    rw [isoPullback_equivariant_assoc ρ q hq f h g _ (ha g) (hb g), hk]
  · intro hk g
    rw [← cancel_epi h.isoPullback.hom,
      ← isoPullback_equivariant_assoc ρ q hq f h g _ (ha g) (hb g)]
    exact hk g

variable {T : Scheme.{u}} (j : T ⟶ S)

/-- Restriction along a base morphism gives a morphism of the actual pullback sources. -/
def baseChangeMap : pullback q (j ≫ f) ⟶ pullback q f :=
  pullback.lift (pullback.fst q (j ≫ f)) (pullback.snd q (j ≫ f) ≫ j)
    (by rw [Category.assoc, pullback.condition])

/-- The first projection is unchanged by restriction of the base. -/
@[reassoc]
lemma baseChangeMap_fst : baseChangeMap q f j ≫ pullback.fst q f =
    pullback.fst q (j ≫ f) := pullback.lift_fst _ _ _

/-- The second projection is the restricted base morphism. -/
@[reassoc]
lemma baseChangeMap_snd : baseChangeMap q f j ≫ pullback.snd q f =
    pullback.snd q (j ≫ f) ≫ j := pullback.lift_snd _ _ _

/-- The canonical base restriction intertwines the two constructed group actions. -/
@[reassoc]
lemma baseChangeMap_equivariant (g : G) :
    (action ρ q hq (j ≫ f) g).hom ≫ baseChangeMap q f j =
      baseChangeMap q f j ≫ (action ρ q hq f g).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeMap_fst, action_fst,
      baseChangeMap_fst_assoc]
  · simp only [Category.assoc, baseChangeMap_snd, action_snd, action_snd_assoc]

end FLT.Mazur.FiniteGroupPullback
