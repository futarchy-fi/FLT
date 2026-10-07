/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeGeometricDescentData

/-!
# Testing a geometric descent cocycle on arbitrary triple charts

Any three compatible pair maps factor through the categorical triple overlap.
Pulling back the actual cocycle therefore gives the equation on those charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open SchemeTripleOverlap SchemeOverlapCocycleChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)

/-- The canonical cocycle holds on every compatible triple of actual pair maps. -/
theorem cocycle_on_pairs (q12 q23 q13 : T ⟶ Limits.pullback p p) (c1 c2 c3 : T ⟶ Y)
    (w12l : q12 ≫ Limits.pullback.fst p p = c1)
    (w12r : q12 ≫ Limits.pullback.snd p p = c2)
    (w23l : q23 ≫ Limits.pullback.fst p p = c2)
    (w23r : q23 ≫ Limits.pullback.snd p p = c3)
    (w13l : q13 ≫ Limits.pullback.fst p p = c1)
    (w13r : q13 ≫ Limits.pullback.snd p p = c3) :
    CocycleCompatible (Limits.pullback.fst p p) (Limits.pullback.snd p p)
      q12 q23 q13 c1 c2 c3 w12l w12r w23l w23r w13l w13r M D.overlap := by
  let t : T ⟶ triple p := Limits.pullback.lift q12 q23 (w12r.trans w23l.symm)
  have ht12 : t ≫ pair12 p = q12 := Limits.pullback.lift_fst _ _ _
  have ht23 : t ≫ pair23 p = q23 := Limits.pullback.lift_snd _ _ _
  have ht1 : t ≫ coord1 p = c1 := by
    rw [coord1, ← Category.assoc, ht12, w12l]
  have ht2 : t ≫ coord2 p = c2 := by
    rw [coord2, ← Category.assoc, ht12, w12r]
  have ht3 : t ≫ coord3 p = c3 := by
    rw [coord3, ← Category.assoc, ht23, w23r]
  have ht13 : t ≫ pair13 p = q13 := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, pair13_fst, ht1, w13l]
    · rw [Category.assoc, pair13_snd, ht3, w13r]
  have h := pullback_cocycle (Limits.pullback.fst p p) (Limits.pullback.snd p p)
    (pair12 p) (pair23 p) (pair13 p) (coord1 p) (coord2 p) (coord3 p)
    rfl rfl (pair23_fst p) rfl (pair13_fst p) (pair13_snd p) M D.overlap
    t c1 c2 c3 ht1 ht2 ht3
    (by rw [ht12]; exact w12l) (by rw [ht12]; exact w12r)
    (by rw [ht23]; exact w23l) (by rw [ht23]; exact w23r)
    (by rw [ht13]; exact w13l) (by rw [ht13]; exact w13r) D.cocycle
  simpa only [ht12, ht23, ht13] using h

end FLT.Mazur.SchemeGeometricDescent.Data
