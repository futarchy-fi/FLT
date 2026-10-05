/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedBaseAlgebra
public import FLT.Mazur.IdealAdicGradedClosedTwist
public import FLT.Mazur.IdealAdicGradedSectionAction

/-!
# The base graded action on the actual closed coefficients

Full faithfulness of closed pushforward transports the constructed sheaf
maps to `closedIdealGraded`. The comparison retains the action on ambient
sheaves, and the unit and composition identities descend with it.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open Scheme.Modules FLT.Mazur.IdealAdicQuotient FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedClosedAction

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- The actual homogeneous sheaf action descended to the closed subscheme. -/
def action (a n : ℕ) (s : Piece I ⊤ a) :
    closedIdealGraded I n ⟶ closedIdealGraded I (a + n) :=
  GlobalClosedModuleDescent.map I (idealGraded_idealKilled I n)
    (idealGraded_idealKilled I (a + n)) (sectionAction I a n s)

/-- Descend degree transport along the same canonical closed comparisons. -/
def reindex {a b : ℕ} (h : a = b) : closedIdealGraded I a ⟶ closedIdealGraded I b :=
  GlobalClosedModuleDescent.map I (idealGraded_idealKilled I a)
    (idealGraded_idealKilled I b) (idealGradedReindex I h)

/-- Closed pushforward recovers the original homogeneous sheaf action. -/
@[reassoc]
lemma action_comparison (a n : ℕ) (s : Piece I ⊤ a) :
    (pushforward I.subschemeι).map (action I a n s) ≫ (closedIdealGradedIso I (a + n)).hom =
      (closedIdealGradedIso I n).hom ≫ sectionAction I a n s :=
  GlobalClosedModuleDescent.map_naturality I _ _ _

/-- The closed coefficients retain the multiplicative composition law. -/
lemma action_mul (a b n : ℕ) (s : Piece I ⊤ a) (t : Piece I ⊤ b) :
    action I (a + b) n (mul I ⊤ a b s t) =
      action I b n t ≫ action I a (b + n) s ≫ reindex I (Nat.add_assoc a b n).symm := by
  unfold action reindex
  rw [sectionAction_mul, GlobalClosedModuleDescent.map_comp,
    GlobalClosedModuleDescent.map_comp]

/-- The original degree-zero unit acts identically on the closed coefficients. -/
lemma action_unit (n : ℕ) :
    action I 0 n (scalar I ⊤ 1) ≫ reindex I (Nat.zero_add n) =
      𝟙 (closedIdealGraded I n) := by
  unfold action reindex
  rw [← GlobalClosedModuleDescent.map_comp, sectionAction_unit,
    GlobalClosedModuleDescent.map_id]
  rfl

/-- Addition of coefficients adds their actions on the closed subscheme. -/
lemma action_add (a n : ℕ) (s t : Piece I ⊤ a) :
    action I a n (s + t) = action I a n s + action I a n t := by
  apply (pushforward I.subschemeι).map_injective
  simp only [action, GlobalClosedModuleDescent.map_pushforward, sectionAction_add,
    Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- A homogeneous base coefficient acts on the actual closed extended-ideal coefficient. -/
def baseAction (a n : ℕ) (s : Piece J ⊤ a) :
    closedIdealGraded (J.comap f) n ⟶ closedIdealGraded (J.comap f) (a + n) :=
  action (J.comap f) a n (IdealAdicGradedPullback.pull J f a ⊤ s)

omit [IsLocallyNoetherian Y] in
/-- The base action agrees with extension followed by the actual ambient multiplication. -/
@[reassoc]
lemma baseAction_comparison (a n : ℕ) (s : Piece J ⊤ a) :
    (pushforward (J.comap f).subschemeι).map (baseAction J f a n s) ≫
      (closedIdealGradedIso (J.comap f) (a + n)).hom =
        (closedIdealGradedIso (J.comap f) n).hom ≫
          sectionAction (J.comap f) a n (IdealAdicGradedPullback.pull J f a ⊤ s) :=
  action_comparison (J.comap f) a n _

/-- Multiplication of base coefficients composes their actions on the closed fibre. -/
lemma baseAction_mul [IsAffine Y] (a b n : ℕ) (s : Piece J ⊤ a) (t : Piece J ⊤ b) :
    baseAction J f (a + b) n (mul J ⊤ a b s t) =
      baseAction J f b n t ≫ baseAction J f a (b + n) s ≫
        reindex (J.comap f) (Nat.add_assoc a b n).symm := by
  unfold baseAction
  rw [IdealAdicGradedPullback.pull_mul J f a b ⟨⊤, isAffineOpen_top Y⟩]
  exact action_mul (J.comap f) a b n _ _

omit [IsLocallyNoetherian Y] in
/-- The base unit acts as the identity on the actual closed graded coefficients. -/
lemma baseAction_unit (n : ℕ) :
    baseAction J f 0 n (scalar J ⊤ 1) ≫ reindex (J.comap f) (Nat.zero_add n) =
      𝟙 (closedIdealGraded (J.comap f) n) := by
  unfold baseAction
  rw [IdealAdicGradedPullback.pull_scalar, map_one]
  exact action_unit (J.comap f) n

omit [IsLocallyNoetherian Y] in
/-- Addition of base coefficients adds their actions on the closed graded sheaf. -/
lemma baseAction_add (a n : ℕ) (s t : Piece J ⊤ a) :
    baseAction J f a n (s + t) = baseAction J f a n s + baseAction J f a n t := by
  unfold baseAction
  have h := ((IdealAdicGradedPullback.gradedMap J f a).app ⊤).hom.map_add s t
  change IdealAdicGradedPullback.pull J f a ⊤ (s + t) =
    IdealAdicGradedPullback.pull J f a ⊤ s + IdealAdicGradedPullback.pull J f a ⊤ t at h
  rw [h, action_add]

end FLT.Mazur.IdealAdicGradedClosedAction
