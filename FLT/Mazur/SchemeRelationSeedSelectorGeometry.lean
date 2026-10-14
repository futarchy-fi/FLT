/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSeedSelectorMap
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Open transition maps between independently selected seed quotients

Etale seed maps induce open immersions of the constructed quotient schemes.
The orbit-fiber comparison also keeps the original point relation, which
will detect intersections during gluing.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSeedSelector.Data
open RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S B C : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  {k : B ⟶ A.left} {l : C ⟶ A.left} (d : Data p q k) (c : Data p q l)
attribute [local irreducible] quotient inclusion projection

include e in
/-- The representative inclusion is itself etale for an etale original seed. -/
theorem inclusion_etale [Etale q.left] [Etale k] : Etale d.inclusion := by
  let _ := d.projection_etale e
  let _ : Etale (d.inclusion ≫ d.projection) := by
    rw [inclusion_projection]
    infer_instance
  exact Etale.of_comp d.inclusion d.projection

include e in
/-- Etale seed refinements give open quotient transitions without matching selectors. -/
theorem map_isOpenImmersion (a : B ⟶ C) (ha : a ≫ l = k)
    [Etale q.left] [Etale k] [Etale l] [Etale a] : IsOpenImmersion (d.map c a) := by
  let _ := d.map_mono c a ha e
  let _ := d.inclusion_etale e
  let _ := c.projection_etale e
  let _ : Etale (d.map c a) := by
    unfold map
    infer_instance
  exact IsOpenImmersion.of_flat_of_mono _

/-- Every seed point is joined to its representative by an actual original arrow. -/
theorem related_representative (x : B) : Related p q (k x) (k (d.rep x)) :=
  ⟨d.arrow x, congrArg (fun a ↦ a x) d.source, congrArg (fun a ↦ a x) d.target⟩

include e in
/-- Equal quotient points belong to the same original orbit. -/
theorem related_of_projection_eq (x y : B) (h : d.projection x = d.projection y) :
    Related p q (k x) (k y) := by
  have hr : d.rep x = d.rep y := by
    have hx := congrArg (fun a ↦ a x) d.projection_inclusion
    have hy := congrArg (fun a ↦ a y) d.projection_inclusion
    exact hx.symm.trans ((congrArg d.inclusion h).trans hy)
  have hh := d.related_representative x
  rw [hr] at hh
  exact related_trans e hh (related_symm e (d.related_representative y))

include e in
/-- The complete quotient fibers are exactly the original orbits meeting this seed. -/
theorem projection_eq_iff_related (x y : B) :
    d.projection x = d.projection y ↔ Related p q (k x) (k y) := by
  refine ⟨d.related_of_projection_eq e x y, ?_⟩
  rintro ⟨z, hx, hy⟩
  obtain ⟨t, ht, htx⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback p.left k) z x hx
  have htq : (pullback.fst p.left k ≫ q.left) t = k y := by
    simpa only [Scheme.Hom.comp_apply, ht] using hy
  obtain ⟨v, hv, hvy⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (pullback.fst p.left k ≫ q.left) k) t y htq
  change pullback.fst (pullback.fst p.left k ≫ q.left) k v = t at hv
  change pullback.snd (pullback.fst p.left k ≫ q.left) k v = y at hvy
  change pullback.snd p.left k t = x at htx
  have h := congrArg (fun a ↦ a v) d.condition
  change d.projection (pullback.snd p.left k
    (pullback.fst (pullback.fst p.left k ≫ q.left) k v)) =
      d.projection (pullback.snd (pullback.fst p.left k ≫ q.left) k v) at h
  rw [hv, htx, hvy] at h
  exact h

end FLT.Mazur.SchemeRelationSeedSelector.Data
