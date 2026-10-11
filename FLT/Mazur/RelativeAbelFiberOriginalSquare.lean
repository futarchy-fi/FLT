/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelRelativeBaseChange
public import FLT.Mazur.RelativeCartierOriginalSquare

/-!
# Full relative Abel fibers on original cartesian squares

Pullback uses the actual supplied total-space morphism and retains the full
ideal. A coefficient isomorphism changes the fiber label without changing
the divisor. Neither operation needs properness or a Noetherian base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}

/-- The Abel class of a full Cartier comap is the original relative Picard pullback. -/
theorem abel_originalSquare (h : IsPullback p q f g) (D : Divisor X)
    (hD : RelativeEffectiveCartier f D.val) :
    abel q ⟨D.val.comap p, (relativeCartier_originalSquare h D.val hD).1⟩ =
      SchemePicard.relativeMap q f p g h.w.symm (abel f D) := by
  let _ := relativeCartierIdealPullback_originalSquare h D.val hD
  change SchemePicard.relativeClass _ _ = SchemePicard.relativeClass _ _
  apply congrArg (SchemePicard.relativeClass q)
  exact SchemePicard.mk_eq_of_iso _ _
    (divisorLinePullbackIsoOfEq p D.property
      (relativeCartier_originalSquare h D.val hD).1 rfl).symm

/-- Pullback on the original full relative fiber for any actual cartesian square. -/
def relativeFiberOriginalPullback (h : IsPullback p q f g)
    (L : X.Modules) (hL : LocallyFreeRankOne L) (D : RelativeFiber f L hL) :
    RelativeFiber q ((pullback p).obj L) (hL.pullback p) := by
  let hD : RelativeEffectiveCartier f D.val.val.val := ⟨D.val.val.property, D.property⟩
  refine ⟨⟨⟨D.val.val.val.comap p, (relativeCartier_originalSquare h _ hD).1⟩, ?_⟩,
    (relativeCartier_originalSquare h _ hD).2⟩
  rw [abel_originalSquare h D.val.val hD, D.val.property]
  rfl

/-- The original-square fiber pullback keeps all equations and nilpotents. -/
lemma relativeFiberOriginalPullback_ideal (h : IsPullback p q f g)
    (L : X.Modules) (hL : LocallyFreeRankOne L) (D : RelativeFiber f L hL) :
    (relativeFiberOriginalPullback h L hL D).val.val.val = D.val.val.val.comap p := rfl

/-- An actual coefficient isomorphism changes only the line label of the relative fiber. -/
def relativeFiberCoefficientEquiv (f : X ⟶ S) {L M : X.Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (e : L ≅ M) :
    RelativeFiber f L hL ≃ RelativeFiber f M hM where
  toFun D := ⟨⟨D.val.val, D.val.property.trans
    (congrArg (SchemePicard.relativeClass f) (SchemePicard.mk_eq_of_iso hL hM e))⟩,
      D.property⟩
  invFun D := ⟨⟨D.val.val, D.val.property.trans
    (congrArg (SchemePicard.relativeClass f) (SchemePicard.mk_eq_of_iso hM hL e.symm))⟩,
      D.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coefficient transport is the identity on the full divisor ideal. -/
lemma relativeFiberCoefficientEquiv_ideal (f : X ⟶ S) {L M : X.Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (e : L ≅ M)
    (D : RelativeFiber f L hL) :
    (relativeFiberCoefficientEquiv f hL hM e D).val.val.val = D.val.val.val := rfl

end FLT.Mazur.CartierAbel
