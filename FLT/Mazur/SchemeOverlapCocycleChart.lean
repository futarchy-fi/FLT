/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapTransportComposition

/-!
# Cocycle equations under a change of double-overlap chart

A triple-overlap test scheme carries three pair maps and three coordinate
maps. Normalizing the double-overlap chart preserves and detects the
cocycle on that test scheme whenever the pair maps lift to the chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapCocycleChart
open SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z Z' T : Scheme.{u}}
variable (l r : Z ⟶ Y) (p12 p23 p13 : T ⟶ Z) (c1 c2 c3 : T ⟶ Y)
variable (w12l : p12 ≫ l = c1) (w12r : p12 ≫ r = c2)
variable (w23l : p23 ≫ l = c2) (w23r : p23 ≫ r = c3)
variable (w13l : p13 ≫ l = c1) (w13r : p13 ≫ r = c3)
variable (M : Y.Modules) (e : (pullback l).obj M ≅ (pullback r).obj M)

/-- The sheaf cocycle tested on three pair maps from a common scheme. -/
def CocycleCompatible : Prop :=
  (normalize l r p12 c1 c2 w12l w12r M e).hom ≫
    (normalize l r p23 c2 c3 w23l w23r M e).hom =
      (normalize l r p13 c1 c3 w13l w13r M e).hom

/-- Changing double-overlap charts preserves and detects the triple-overlap cocycle. -/
theorem normalize_cocycle_iff (k : Z' ⟶ Z) (l' r' : Z' ⟶ Y)
    (wl : k ≫ l = l') (wr : k ≫ r = r') (q12 q23 q13 : T ⟶ Z')
    (v12 : q12 ≫ k = p12) (v23 : q23 ≫ k = p23) (v13 : q13 ≫ k = p13)
    (u12l : q12 ≫ l' = c1) (u12r : q12 ≫ r' = c2)
    (u23l : q23 ≫ l' = c2) (u23r : q23 ≫ r' = c3)
    (u13l : q13 ≫ l' = c1) (u13r : q13 ≫ r' = c3) :
    CocycleCompatible l' r' q12 q23 q13 c1 c2 c3 u12l u12r u23l u23r u13l u13r
        M (normalize l r k l' r' wl wr M e) ↔
      CocycleCompatible l r p12 p23 p13 c1 c2 c3 w12l w12r w23l w23r w13l w13r M e := by
  unfold CocycleCompatible
  rw [normalize_comp_of_eq l r k l' r' wl wr q12 p12 v12 c1 c2 u12l u12r w12l w12r,
    normalize_comp_of_eq l r k l' r' wl wr q23 p23 v23 c2 c3 u23l u23r w23l w23r,
    normalize_comp_of_eq l r k l' r' wl wr q13 p13 v13 c1 c3 u13l u13r w13l w13r]

end FLT.Mazur.SchemeOverlapCocycleChart
