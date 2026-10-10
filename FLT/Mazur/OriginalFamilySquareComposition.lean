/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquareInversePasting

/-!
# Composition of the original twisting-line square maps

The forward path comparisons used in direct section pullback agree with the
inverse square comparisons, and therefore inherit their actual pasting law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackPathComparison
open SchemePullbackSquare
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P Q R T U V : Scheme.{u}}

/-- The original forward path is exactly the inverse square comparison. -/
lemma comparison_square_inv (q : P ⟶ T) (q' : Q ⟶ U) (k : U ⟶ T)
    (r : Q ⟶ P) (h : r ≫ q = q' ≫ k) (N : T.Modules) :
    (comparison r q (q' ≫ k) h).hom.app N ≫ (pullbackComp q' k).inv.app N =
      (squareIso q q' k r h.symm).inv.app N := by
  simp only [squareIso, comparison, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    NatTrans.comp_app, pullbackCongr, eqToIso.hom, eqToIso.inv,
    Category.assoc]

/-- Pasting the original square paths keeps the actual total and base comparisons. -/
@[reassoc]
lemma original_square_comp (q : P ⟶ T) (q' : Q ⟶ U) (q'' : R ⟶ V)
    (k : U ⟶ T) (l : V ⟶ U) (r : Q ⟶ P) (s : R ⟶ Q)
    (h : r ≫ q = q' ≫ k) (h' : s ≫ q' = q'' ≫ l)
    (hc : (s ≫ r) ≫ q = q'' ≫ (l ≫ k)) (N : T.Modules) :
    (pullback s).map ((comparison r q (q' ≫ k) h).hom.app N ≫
      (pullbackComp q' k).inv.app N) ≫
      ((comparison s q' (q'' ≫ l) h').hom.app ((pullback k).obj N) ≫
        (pullbackComp q'' l).inv.app ((pullback k).obj N)) ≫
      (pullback q'').map ((pullbackComp l k).hom.app N) =
    (pullbackComp s r).hom.app ((pullback q).obj N) ≫
      (comparison (s ≫ r) q (q'' ≫ (l ≫ k)) hc).hom.app N ≫
      (pullbackComp q'' (l ≫ k)).inv.app N := by
  rw [comparison_square_inv, comparison_square_inv, ← Category.assoc,
    comparison_square_inv]
  exact squareIso_inv_paste r q' q k h.symm s q'' l h'.symm N

end FLT.Mazur.SheafPullbackPathComparison
