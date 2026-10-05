/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCanonicalOverlapNaturality

/-!
# Recognition of maps between reconstructed overlaps

A reconstruction square intertwines any overlaps identified with the canonical ones.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (l r : Z ⟶ Y) (k : Z ⟶ X)
variable (hl : l ≫ p = k) (hr : r ≫ p = k)
variable {A B : X.Modules} {M N : Y.Modules}

/-- Equality with canonical overlaps turns reconstruction into overlap compatibility. -/
theorem compatible_of_chartOverlap_eq
    (e : (pullback p).obj A ≅ M) (e' : (pullback p).obj B ≅ N)
    (d : (pullback l).obj M ≅ (pullback r).obj M)
    (d' : (pullback l).obj N ≅ (pullback r).obj N)
    (hd : d = chartOverlap p l r k hl hr A e)
    (hd' : d' = chartOverlap p l r k hl hr B e')
    (g : A ⟶ B) (f : M ⟶ N)
    (h : (pullback p).map g ≫ e'.hom = e.hom ≫ f) :
    d.hom ≫ (pullback r).map f = (pullback l).map f ≫ d'.hom := by
  rw [hd, hd']
  exact chartOverlap_compatible p l r k hl hr e e' g f h

end FLT.Mazur.SchemePullbackOverlap
