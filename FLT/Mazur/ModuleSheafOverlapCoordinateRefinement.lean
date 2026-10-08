/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapImageTransition
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Refinement of overlap coordinates

The recovery of a chart module from its ambient pushforward commutes with
further pullback and normalization of the coordinate paths.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOverlapImageTransition

open SheafPullbackPathComparison SheafPullbackMapNormalization

variable {W O X Y Z : Scheme.{u}}

/-- Recovering a chart module commutes with refinement of the overlap. -/
@[reassoc]
lemma coordinateIso_refine (t : W ⟶ O) (p : O ⟶ Y) (i : Y ⟶ X)
    [IsOpenImmersion i] (r : O ⟶ X) (h : p ≫ i = r)
    (p' : W ⟶ Y) (r' : W ⟶ X) (hp : t ≫ p = p') (hr : t ≫ r = r')
    (h' : p' ≫ i = r') (M : Y.Modules) :
    (pullback t).map (coordinateIso p i r h M).hom ≫
        (comparison t p p' hp).hom.app M =
      (comparison t r r' hr).hom.app ((pushforward i).obj M) ≫
        (coordinateIso p' i r' h' M).hom := by
  apply (cancel_epi ((pullback t).map
    ((comparison p i r h).hom.app ((pushforward i).obj M)))).mp
  simp only [coordinateIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc, comparison_assoc t p i p' r r' hp h hr h']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (comparison t p p' hp).hom.naturality (openCounitIso i M).hom

/-- Refining an ambient overlap map recovers the normalized coordinate comparison. -/
@[reassoc]
lemma ambientIso_refine_coordinate (t : W ⟶ O)
    (i : Y ⟶ X) (j : Z ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (p : O ⟶ Y) (q : O ⟶ Z) (r : O ⟶ X)
    (hi : p ≫ i = r) (hj : q ≫ j = r)
    (p' : W ⟶ Y) (q' : W ⟶ Z) (r' : W ⟶ X)
    (hp : t ≫ p = p') (hq : t ≫ q = q') (hr : t ≫ r = r')
    (hi' : p' ≫ i = r') (hj' : q' ≫ j = r')
    {M : Y.Modules} {N : Z.Modules}
    (e : (pullback p).obj M ≅ (pullback q).obj N) :
    normalize t r r r' r' hr hr (ambientIso i j p q r hi hj e).hom ≫
        (coordinateIso q' j r' hj' N).hom =
      (coordinateIso p' i r' hi' M).hom ≫
        normalize t p q p' q' hp hq e.hom := by
  apply (cancel_epi ((comparison t r r' hr).hom.app ((pushforward i).obj M))).mp
  rw [normalize_comm_assoc, ← coordinateIso_refine t q j r hj q' r' hq hr hj',
    ← Functor.map_comp_assoc, ambientIso_coordinate, Functor.map_comp, Category.assoc,
    ← normalize_comm, ← Category.assoc, coordinateIso_refine, Category.assoc]

end FLT.Mazur.ModuleSheafOverlapImageTransition
