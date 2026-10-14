/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorDiagram
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Actual intersections of independently selected quotient charts

Original orbit fibers and invariance of the source opens show that every
identified pair of quotient points lifts to an actual intersection chart.
This proves the local directedness required for scheme gluing.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
open RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- Pointwise transition naturality retains the literal original source inclusion. -/
theorem transition_projection {U V : Chart p q} (h : U ≤ V) (x : U.val.val.toScheme) :
    transition p q h ((selector p q U).projection x) =
      (selector p q V).projection (A.left.homOfLE h x) :=
  congrArg (fun a ↦ a x) (projection_transition p q h)

include e in
/-- Equality in a larger quotient forces the original representative into the other open. -/
theorem mem_of_transition_eq {U V W : Chart p q} (hU : U ≤ W) (hV : V ≤ W)
    (x : U.val.val.toScheme) (y : V.val.val.toScheme)
    (h : transition p q hU ((selector p q U).projection x) =
      transition p q hV ((selector p q V).projection y)) : x.val ∈ V.val.val := by
  rw [transition_projection, transition_projection] at h
  have hr := (selector p q W).related_of_projection_eq e
    (A.left.homOfLE hU x) (A.left.homOfLE hV y) h
  have hx : W.val.val.ι (A.left.homOfLE hU x) = x.val :=
    congrArg (fun a ↦ a x) (Scheme.homOfLE_ι A.left hU)
  have hy : W.val.val.ι (A.left.homOfLE hV y) = y.val :=
    congrArg (fun a ↦ a y) (Scheme.homOfLE_ι A.left hV)
  rw [hx, hy] at hr
  exact (invariant_mem_iff V.val hr).mpr y.property

include e in
/-- Actual source intersections supply all overlaps in the quotient diagram. -/
instance diagram_isLocallyDirected [Etale q.left] :
    (diagram p q e ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro U V W hU hV z w hzw
  change transition p q (leOfHom hU) z = transition p q (leOfHom hV) w at hzw
  obtain ⟨x, rfl⟩ := (selector p q U).projection.surjective z
  obtain ⟨y, rfl⟩ := (selector p q V).projection.surjective w
  have hx := mem_of_transition_eq e (leOfHom hU) (leOfHom hV) x y hzw
  let T := intersection p q U V
  let t : T.val.val.toScheme := ⟨x.val, x.property, hx⟩
  have ht : transition p q (intersection_le_left p q U V)
      ((selector p q T).projection t) = (selector p q U).projection x := by
    rw [transition_projection]
    apply congrArg (selector p q U).projection
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _
  refine ⟨T, homOfLE (intersection_le_left p q U V),
    homOfLE (intersection_le_right p q U V), (selector p q T).projection t, ht, ?_⟩
  let _ := transition_isOpenImmersion p q e (leOfHom hV)
  apply (transition p q (leOfHom hV)).isOpenEmbedding.injective
  change (transition p q (intersection_le_right p q U V) ≫
    transition p q (leOfHom hV)) _ = _
  rw [transition_trans]
  have hc : transition p q ((intersection_le_right p q U V).trans (leOfHom hV)) =
      transition p q (intersection_le_left p q U V) ≫ transition p q (leOfHom hU) :=
    (transition_trans p q _ _).symm
  rw [hc, Scheme.Hom.comp_apply, ht]
  exact hzw

end FLT.Mazur.SchemeRelationOpenSelector
