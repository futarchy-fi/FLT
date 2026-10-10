/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalCocycle

/-!
# Detecting canonical pair compatibility on an alternate chart

An original pair can map to another common chart. Compatibility there pulls
back and normalizes to compatibility on the actual original fiber product.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentCanonicalOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y₁ Y₂ Z : Scheme.{u}}

/-- Compatibility on a common chart gives the original canonical pair equation. -/
lemma pair_compatible_of_chart (f : Y₁ ⟶ X) (g : Y₂ ⟶ X)
    (l : Z ⟶ Y₁) (r : Z ⟶ Y₂) (k : Z ⟶ X) (wl : l ≫ f = k) (wr : r ≫ g = k)
    (t : Limits.pullback f g ⟶ Z)
    (tl : t ≫ l = Limits.pullback.fst f g) (tr : t ≫ r = Limits.pullback.snd f g)
    (A B : X.Modules)
    (a : (pullback f).obj A ⟶ (pullback f).obj B)
    (b : (pullback g).obj A ⟶ (pullback g).obj B)
    (h : (overlap f g l r k wl wr A).hom ≫ (pullback r).map b =
      (pullback l).map a ≫ (overlap f g l r k wl wr B).hom) :
    (pair f g A).hom ≫ (pullback (Limits.pullback.snd f g)).map b =
      (pullback (Limits.pullback.fst f g)).map a ≫ (pair f g B).hom := by
  have hh := SchemeIndependentPairNormalization.normalize_compatible l r t
    (Limits.pullback.fst f g) (Limits.pullback.snd f g) tl tr
    (overlap f g l r k wl wr A) (overlap f g l r k wl wr B) a b h
  rw [normalize_overlap f g l r k wl wr t _ _ tl tr
    (Limits.pullback.fst f g ≫ f) rfl Limits.pullback.condition.symm,
    normalize_overlap f g l r k wl wr t _ _ tl tr
    (Limits.pullback.fst f g ≫ f) rfl Limits.pullback.condition.symm] at hh
  exact hh

end FLT.Mazur.SchemeIndependentCanonicalOverlap
