/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeDescentTransportSquares

/-!
# Cross-cover transport intertwines the actual refined data

Two covering-chart maps over the same base chart need not agree. The original
cocycle shows that transport between them is a morphism of their two refined
descent data. This is the compatibility needed for effective affine descent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules} (D : Data p M)
variable (q : Y' ⟶ X') (a : X' ⟶ X) (b c : Y' ⟶ Y)
variable (wb : q ≫ a = b ≫ p) (wc : q ≫ a = c ≫ p)

/-- Cross-cover transport is compatible with the actual two refined overlap isomorphisms. -/
theorem transport_refine_compatible :
    (D.refine p q a b wb).MapCompatible q (D.refine p q a c wc)
      (D.transport b c (wb.symm.trans wc)).hom := by
  have hl : (Limits.pullback.fst q q ≫ b) ≫ p =
      (Limits.pullback.fst q q ≫ c) ≫ p := by
    simp only [Category.assoc, ← wb, ← wc]
  have hr : (Limits.pullback.snd q q ≫ b) ≫ p =
      (Limits.pullback.snd q q ≫ c) ≫ p := by
    simp only [Category.assoc, ← wb, ← wc]
  have hb := refinement_pair_condition q a b wb
  have hc := refinement_pair_condition q a c wc
  unfold MapCompatible
  apply (cancel_mono ((pullbackComp (Limits.pullback.snd q q) c).hom.app M)).mp
  simp only [Category.assoc]
  rw [D.transport_pullback_hom b c (wb.symm.trans wc) _ hr,
    D.refine_overlap_transport_hom q a c wc,
    D.refine_overlap_transport_hom_assoc q a b wb,
    D.transport_pullback_hom_assoc b c (wb.symm.trans wc) _ hl]
  rw [D.transport_rectangle _ _ _ _ hb hr hl hc]

end FLT.Mazur.SchemeGeometricDescent.Data
