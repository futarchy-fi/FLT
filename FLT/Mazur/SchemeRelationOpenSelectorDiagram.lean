/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorRestriction

/-!
# The diagram of all invariant opens admitting original representatives

Each object independently chooses its representatives. The quotient maps
nevertheless form a functor with open transition maps. Intersections remain
objects because restriction constructs the required representative arrows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
open RelativeRelationOrbit SchemeRelationSeedSelector
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} (p q : D ⟶ A)

/-- Actual invariant source opens on which original representative arrows exist. -/
abbrev Chart := {U : InvariantOpens p q // Nonempty (Data p q U.val.ι)}

/-- Choose representatives independently on each chart. -/
def selector (U : Chart p q) : Data p q U.val.val.ι := Classical.choice U.property

/-- Quotient transition maps require only inclusion of the original source opens. -/
def transition {U V : Chart p q} (h : U ≤ V) :
    (selector p q U).quotient ⟶ (selector p q V).quotient :=
  (selector p q U).map (selector p q V) (A.left.homOfLE h)

@[reassoc]
theorem projection_transition {U V : Chart p q} (h : U ≤ V) :
    (selector p q U).projection ≫ transition p q h =
      A.left.homOfLE h ≫ (selector p q V).projection :=
  (selector p q U).projection_map (selector p q V) _ (Scheme.homOfLE_ι A.left h)

/-- The transition attached to an identity inclusion is the identity. -/
theorem transition_refl (U : Chart p q) : transition p q (le_refl U) = 𝟙 _ := by
  have h : A.left.homOfLE (show U.val.val ≤ U.val.val from le_rfl) = 𝟙 _ := by
    apply (cancel_mono U.val.val.ι).mp
    rw [Scheme.homOfLE_ι, Category.id_comp]
  unfold transition
  rw [h, Data.map_id]

/-- The transition maps satisfy strict composition without matching representatives. -/
@[reassoc]
theorem transition_trans {U V W : Chart p q} (h : U ≤ V) (t : V ≤ W) :
    transition p q h ≫ transition p q t = transition p q (h.trans t) := by
  unfold transition
  rw [Data.map_comp _ _ _ (Scheme.homOfLE_ι A.left h) _ _ (Scheme.homOfLE_ι A.left t),
    Scheme.homOfLE_homOfLE]

/-- The actual quotient schemes form a diagram on the original invariant opens. -/
def diagram (_e : CategoryTheory.EquivalenceRelation p q) : Chart p q ⥤ Scheme.{u} where
  obj U := (selector p q U).quotient
  map h := transition p q (leOfHom h)
  map_id U := transition_refl p q U
  map_comp h t := (transition_trans p q (leOfHom h) (leOfHom t)).symm

/-- Invariant opens are closed under intersection. -/
def invariantIntersection (U V : InvariantOpens p q) : InvariantOpens p q :=
  ⟨U.val ⊓ V.val, by
    change (p.left ⁻¹ᵁ U.val) ⊓ (p.left ⁻¹ᵁ V.val) =
      (q.left ⁻¹ᵁ U.val) ⊓ (q.left ⁻¹ᵁ V.val)
    rw [U.property, V.property]⟩

/-- Restriction constructs representatives on each actual chart intersection. -/
def intersection (U V : Chart p q) : Chart p q :=
  ⟨invariantIntersection p q U.val V.val,
    ⟨(selector p q U).restrict (invariantIntersection p q U.val V.val) inf_le_left⟩⟩

theorem intersection_le_left (U V : Chart p q) : intersection p q U V ≤ U :=
  show U.val.val ⊓ V.val.val ≤ U.val.val from inf_le_left

theorem intersection_le_right (U V : Chart p q) : intersection p q U V ≤ V :=
  show U.val.val ⊓ V.val.val ≤ V.val.val from inf_le_right

variable (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]

include e in
/-- Every quotient transition is an open immersion proved from the original etale relation. -/
theorem transition_isOpenImmersion {U V : Chart p q} (h : U ≤ V) :
    IsOpenImmersion (transition p q h) :=
  (selector p q U).map_isOpenImmersion e (selector p q V) _ (Scheme.homOfLE_ι A.left h)

/-- Open transitions are available to the scheme gluing API. -/
instance diagram_map_isOpenImmersion {U V : Chart p q} (h : U ⟶ V) :
    IsOpenImmersion ((diagram p q e).map h) := transition_isOpenImmersion p q e (leOfHom h)

end FLT.Mazur.SchemeRelationOpenSelector
