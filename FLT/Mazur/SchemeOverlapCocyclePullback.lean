/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapCocycleChart

/-!
# Pulling back triple-overlap cocycle equations

Normalized pullback preserves composition of overlap isomorphisms. Thus a
cocycle tested on one triple-overlap scheme remains valid after restriction
to another test scheme, with the coordinate comparison isomorphisms included.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapCocycleChart
open SchemeOverlapDiagonalChart SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z T T' : Scheme.{u}}

/-- Normalized pullback preserves an equation composing three coordinate isomorphisms. -/
theorem normalize_hom_comp (c1 c2 c3 : T ⟶ Y) (t : T' ⟶ T)
    (d1 d2 d3 : T' ⟶ Y) (w1 : t ≫ c1 = d1) (w2 : t ≫ c2 = d2)
    (w3 : t ≫ c3 = d3) (M : Y.Modules)
    (e12 : (pullback c1).obj M ≅ (pullback c2).obj M)
    (e23 : (pullback c2).obj M ≅ (pullback c3).obj M)
    (e13 : (pullback c1).obj M ≅ (pullback c3).obj M)
    (h : e12.hom ≫ e23.hom = e13.hom) :
    (normalize c1 c2 t d1 d2 w1 w2 M e12).hom ≫
      (normalize c2 c3 t d2 d3 w2 w3 M e23).hom =
    (normalize c1 c3 t d1 d3 w1 w3 M e13).hom := by
  dsimp only [SchemeOverlapDiagonalChart.normalize, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, h]

variable (l r : Z ⟶ Y) (p12 p23 p13 : T ⟶ Z) (c1 c2 c3 : T ⟶ Y)
variable (w12l : p12 ≫ l = c1) (w12r : p12 ≫ r = c2)
variable (w23l : p23 ≫ l = c2) (w23r : p23 ≫ r = c3)
variable (w13l : p13 ≫ l = c1) (w13r : p13 ≫ r = c3)
variable (M : Y.Modules) (e : (pullback l).obj M ≅ (pullback r).obj M)

/-- Restricting the triple-overlap test scheme preserves the geometric cocycle. -/
theorem pullback_cocycle (t : T' ⟶ T) (d1 d2 d3 : T' ⟶ Y)
    (w1 : t ≫ c1 = d1) (w2 : t ≫ c2 = d2) (w3 : t ≫ c3 = d3)
    (u12l : (t ≫ p12) ≫ l = d1) (u12r : (t ≫ p12) ≫ r = d2)
    (u23l : (t ≫ p23) ≫ l = d2) (u23r : (t ≫ p23) ≫ r = d3)
    (u13l : (t ≫ p13) ≫ l = d1) (u13r : (t ≫ p13) ≫ r = d3)
    (h : CocycleCompatible l r p12 p23 p13 c1 c2 c3
      w12l w12r w23l w23r w13l w13r M e) :
    CocycleCompatible l r (t ≫ p12) (t ≫ p23) (t ≫ p13) d1 d2 d3
      u12l u12r u23l u23r u13l u13r M e := by
  have hh := normalize_hom_comp c1 c2 c3 t d1 d2 d3 w1 w2 w3 M
    (normalize l r p12 c1 c2 w12l w12r M e)
    (normalize l r p23 c2 c3 w23l w23r M e)
    (normalize l r p13 c1 c3 w13l w13r M e) h
  rw [normalize_comp l r p12 c1 c2 w12l w12r t d1 d2 w1 w2 u12l u12r,
    normalize_comp l r p23 c2 c3 w23l w23r t d2 d3 w2 w3 u23l u23r,
    normalize_comp l r p13 c1 c3 w13l w13r t d1 d3 w1 w3 u13l u13r] at hh
  exact hh

end FLT.Mazur.SchemeOverlapCocycleChart
