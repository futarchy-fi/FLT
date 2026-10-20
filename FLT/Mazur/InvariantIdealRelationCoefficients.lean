/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafClosedTransitions
public import FLT.Mazur.InvariantIdealRelation
public import FLT.Mazur.SchemeRelationInvariantFunctorial

/-!
# Full boundary invariant pullback under exact ideal transport

A map of both independent relation endpoints and an exact pulled ideal give
an actual map on the whole boundary relation and its invariant coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.InvariantIdealRelationCoefficients
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A D' A' : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (hp : b ≫ p = p' ≫ a) (hq : b ≫ q = q' ≫ a)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  (I : A'.IdealSheafData) (hI : I.comap p' = I.comap q') (hIJ : J.comap a = I)
set_option quotPrecheck false
local notation "c" => IdealSheafClosedTransitions.map I J a hIJ
local notation "r" => pullback.snd p J.subschemeι
local notation "s" => InvariantIdealRelation.snd J p q hJ
local notation "r'" => pullback.snd p' I.subschemeι
local notation "s'" => InvariantIdealRelation.snd I p' q' hI

/-- The whole closed first-endpoint relation maps to the original closed relation. -/
def arrow : pullback p' I.subschemeι ⟶ pullback p J.subschemeι :=
  pullback.lift (pullback.fst p' I.subschemeι ≫ b) (r' ≫ c) (by
    rw [Category.assoc, hp, ← Category.assoc, pullback.condition,
      Category.assoc, Category.assoc, IdealSheafClosedTransitions.map_inclusion])

/-- First boundary endpoints commute with the exact ideal map. -/
@[reassoc]
theorem arrow_first : arrow p p' a b hp J I hIJ ≫ r = r' ≫ c :=
  pullback.lift_snd _ _ _

include hq in
/-- Independent second boundary endpoints commute with the same exact ideal map. -/
@[reassoc]
theorem arrow_second : arrow p p' a b hp J I hIJ ≫ s = s' ≫ c := by
  apply (cancel_mono J.subschemeι).mp
  rw [Category.assoc, InvariantIdealRelation.snd_ι,
    arrow, pullback.lift_fst_assoc, Category.assoc, hq,
    Category.assoc, IdealSheafClosedTransitions.map_inclusion,
    ← Category.assoc s', InvariantIdealRelation.snd_ι, Category.assoc]

/-- Pullback of full boundary invariants through the literal boundary scheme map. -/
def restriction : compatibleFunctions r s →+* compatibleFunctions r' s' :=
  relationPullback r s r' s' c (arrow p p' a b hp J I hIJ)
    (arrow_first p p' a b hp J I hIJ) (arrow_second p q p' q' a b hp hq J hJ I hI hIJ)

/-- The underlying coefficient is restriction along the exact closed ideal map. -/
theorem restriction_val (t : compatibleFunctions r s) :
    (restriction p q p' q' a b hp hq J hJ I hI hIJ t).val = (c).appTop t.val := rfl

end FLT.Mazur.InvariantIdealRelationCoefficients
