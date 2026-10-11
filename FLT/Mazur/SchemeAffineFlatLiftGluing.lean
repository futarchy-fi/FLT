/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Gluing lifts characterized on flat affine restrictions

Affine local lifts with the same contraction glue when each is unique
on flat affine restrictions. The resulting uniqueness persists after
flat base change by any scheme, using the pulled-back affine cover.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemeAffineFlatLiftGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y Z : Scheme.{u}} (C : X.AffineOpenCover)
  (l : ∀ i, Spec (C.X i) ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z)
  (hl : ∀ i, l i ≫ q = C.f i ≫ r)
  (hu : ∀ (i : C.I₀) {S : Type u} [CommRing S]
    (p : Spec (.of S) ⟶ Spec (C.X i)) [Flat p]
    (a : Spec (.of S) ⟶ Y), a ≫ q = p ≫ l i ≫ q → a = p ≫ l i)

include hl hu in
/-- Flat affine uniqueness identifies local lifts on their full intersections. -/
theorem compatible (i j : C.I₀) :
    pullback.fst (C.f i) (C.f j) ≫ l i = pullback.snd (C.f i) (C.f j) ≫ l j := by
  let V := pullback (C.f i) (C.f j)
  apply V.affineCover.hom_ext
  intro k
  symm
  rw [← Category.assoc]
  apply hu i (V.affineCover.f k ≫ pullback.fst (C.f i) (C.f j))
  simp only [Category.assoc, hl]
  rw [pullback.condition_assoc]

include hu in
/-- Flat affine uniqueness also detects lifts after arbitrary flat scheme base change. -/
theorem flat_unique (L : X ⟶ Y) (hL : ∀ i, C.f i ≫ L = l i)
    {T : Scheme.{u}} (p : T ⟶ X) [Flat p] (a : T ⟶ Y)
    (ha : a ≫ q = p ≫ L ≫ q) : a = p ≫ L := by
  apply (show T.OpenCover from C.openCover.pullback₁ p).hom_ext
  intro i
  apply (pullback p (C.f i)).affineCover.hom_ext
  intro j
  let t := (pullback p (C.f i)).affineCover.f j
  change t ≫ pullback.fst p (C.f i) ≫ a = t ≫ pullback.fst p (C.f i) ≫ p ≫ L
  have he : (t ≫ pullback.snd p (C.f i)) ≫ l i =
      t ≫ pullback.fst p (C.f i) ≫ p ≫ L := by
    rw [← hL]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc]
  rw [← he]
  apply hu i (t ≫ pullback.snd p (C.f i))
  simpa only [Category.assoc, ha] using congrArg (fun z => z ≫ q) he.symm

end FLT.Mazur.SchemeAffineFlatLiftGluing
