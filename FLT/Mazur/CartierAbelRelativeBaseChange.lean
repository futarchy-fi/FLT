/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelFiber
public import FLT.Mazur.RelativeCartierDivisorPullback

/-!
# Arbitrary test-base change of actual Cartier Abel fibers

Relative Cartier divisors survive arbitrary base change. The actual positive
line comparison proves that their Abel classes pull back in the relative
Picard group, giving a map between the corresponding fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S T : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S)

/-- The actual pulled divisor, retaining its full ideal sheaf. -/
def divisorBaseChange (D : Divisor X) (hD : RelativeEffectiveCartier f D.val) :
    Divisor (Limits.pullback f g) :=
  ⟨D.val.comap (Limits.pullback.fst f g), (relativeCartierBaseChange f g D.val hD).1⟩

/-- The Cartier Abel map commutes with arbitrary relative base change. -/
theorem abel_baseChange (D : Divisor X) (hD : RelativeEffectiveCartier f D.val) :
    abel (Limits.pullback.snd f g) (divisorBaseChange f g D hD) =
      SchemePicard.relativeMap (Limits.pullback.snd f g) f
        (Limits.pullback.fst f g) g (Limits.pullback.condition.symm) (abel f D) := by
  change SchemePicard.relativeClass _ _ = SchemePicard.relativeClass _ _
  apply congrArg (SchemePicard.relativeClass (Limits.pullback.snd f g))
  exact SchemePicard.mk_eq_of_iso _ _ (relativeCartierDivisorPullbackIso f g D.val hD).symm

/-- The relative part of the Cartier Abel fiber consists of divisors flat over the test base. -/
def RelativeFiber (L : X.Modules) (hL : LocallyFreeRankOne L) :=
  {D : Fiber f L hL // Flat (D.val.val.subschemeι ≫ f)}

/-- Arbitrary test-base change of the actual relative Abel fiber. -/
def fiberBaseChange (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : RelativeFiber f L hL) :
    RelativeFiber (Limits.pullback.snd f g) ((pullback (Limits.pullback.fst f g)).obj L)
      (hL.pullback (Limits.pullback.fst f g)) := by
  let hD : RelativeEffectiveCartier f D.val.val.val := ⟨D.val.val.property, D.property⟩
  refine ⟨⟨divisorBaseChange f g D.val.val hD, ?_⟩,
    (relativeCartierBaseChange f g D.val.val.val hD).2⟩
  rw [abel_baseChange, D.val.property]
  rfl

/-- The fiber map is the usual comap of the original full ideal. -/
lemma fiberBaseChange_ideal (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : RelativeFiber f L hL) :
    (fiberBaseChange f g L hL D).val.val.val =
      D.val.val.val.comap (Limits.pullback.fst f g) := rfl

end FLT.Mazur.CartierAbel
