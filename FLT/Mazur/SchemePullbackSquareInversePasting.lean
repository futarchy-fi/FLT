/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquarePasting

/-!
# Pasting inverse square comparisons

The inverse comparisons are the direction used to pull original twisting
lines. Their pasting law retains both prescribed composition comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {Q P X U T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (a : Q ⟶ P) (b : Q ⟶ U) (h : U ⟶ T)
  (v : b ≫ h = a ≫ q)

/-- Pasting the inverse square comparisons preserves the actual base composition. -/
@[reassoc]
lemma squareIso_inv_paste (M : S.Modules) :
    (pullback a).map ((squareIso f q g p w).inv.app M) ≫
      (squareIso q b h a v).inv.app ((pullback g).obj M) ≫
      (pullback b).map ((pullbackComp h g).hom.app M) =
    (pullbackComp a p).hom.app ((pullback f).obj M) ≫
      (squareIso f b (h ≫ g) (a ≫ p) (paste_eq p q f g w a b h v)).inv.app M := by
  apply (cancel_mono
    ((squareIso f b (h ≫ g) (a ≫ p) (paste_eq p q f g w a b h v)).hom.app M)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [squareIso_paste p q f g w a b h v]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end FLT.Mazur.SchemePullbackSquare
