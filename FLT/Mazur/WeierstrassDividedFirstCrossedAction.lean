/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeAffineLiftUniqueness
public import FLT.Mazur.WeierstrassDividedFirstExteriorCenter
public import FLT.Mazur.WeierstrassDividedFirstInfinityCenter
public import FLT.Mazur.WeierstrassDividedFirstUnitAction

/-!
# Glued successor actions on both crossed retained-input branches

The infinity and preceding exterior inputs have proved unit output centers.
Their actual affine lifts glue on the whole branches and remain unique
after arbitrary scheme restriction, including nonflat restrictions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)

local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstDividedAffineCover hπ data hn

local notation "D" => firstDividedInputCover hπ data hn
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
/-- The two crossed retained branches have unit successive output centers. -/
theorem firstDividedCrossed_center (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) (a : ((D).X j).affineCover.I₀) :
    (I).map (firstDividedAlpha hπ data hn ⟨j, a⟩) = ⊤ := by
  rcases hj with rfl | rfl
  · exact firstDividedInfinity_center hπ data hn a
  · exact firstDividedExterior_center hπ data hn a

/-- The actual affine action on an infinity or retained exterior input with divided output. -/
def firstDividedCrossedAffineAction (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) (a : ((D).X j).affineCover.I₀) :
    ((D).X j).affineCover.X a ⟶ finiteGlobalModel hπ data 1 hn :=
  firstDividedUnitAction hπ data hn ⟨j, a⟩ (firstDividedCrossed_center hπ data hn j hj a)

/-- Each affine crossed lift has exactly the prescribed divided output. -/
@[reassoc] theorem firstDividedCrossedAffineAction_step (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) (a : ((D).X j).affineCover.I₀) :
    firstDividedCrossedAffineAction hπ data hn j hj a ≫ finiteGlobalStep hπ data 0 hn =
      ((D).X j).affineCover.f a ≫ (D).f j ≫ pullback.snd _ _ ≫ v := by
  rw [firstDividedCrossedAffineAction, firstDividedUnitAction_step]
  exact Category.assoc _ _ _

/-- Every affine restriction of a crossed lift is uniquely determined by its step. -/
theorem firstDividedCrossedAffineAction_unique (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) (a : ((D).X j).affineCover.I₀)
    {S : Type u} [CommRing S] (p : Spec (.of S) ⟶ ((D).X j).affineCover.X a)
    (b : Spec (.of S) ⟶ finiteGlobalModel hπ data 1 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstDividedCrossedAffineAction hπ data hn j hj a ≫ finiteGlobalStep hπ data 0 hn) :
    b = p ≫ firstDividedCrossedAffineAction hπ data hn j hj a :=
  firstDividedUnitAction_affine_unique hπ data hn ⟨j, a⟩
    (firstDividedCrossed_center hπ data hn j hj a) p b hb

/-- The actual crossed affine actions agree on their entire scheme intersections. -/
theorem firstDividedCrossedAffineAction_overlap (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) (a b : ((D).X j).affineCover.I₀) :
    pullback.fst (((D).X j).affineCover.f a) (((D).X j).affineCover.f b) ≫
        firstDividedCrossedAffineAction hπ data hn j hj a =
      pullback.snd (((D).X j).affineCover.f a) (((D).X j).affineCover.f b) ≫
        firstDividedCrossedAffineAction hπ data hn j hj b :=
  SchemeAffineLiftUniqueness.compatible ((D).X j).affineOpenCover
    (firstDividedCrossedAffineAction hπ data hn j hj) (finiteGlobalStep hπ data 0 hn)
    ((D).f j ≫ pullback.snd _ _ ≫ v)
    (firstDividedCrossedAffineAction_step hπ data hn j hj)
    (fun a _ _ p b hb => firstDividedCrossedAffineAction_unique hπ data hn j hj a p b hb) a b

/-- The actual whole crossed-branch action, constructed from its proved affine lifts. -/
irreducible_def firstDividedCrossedAction (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) : (D).X j ⟶ finiteGlobalModel hπ data 1 hn :=
  ((D).X j).affineCover.glueMorphisms (firstDividedCrossedAffineAction hπ data hn j hj)
    (firstDividedCrossedAffineAction_overlap hπ data hn j hj)

/-- Restricting the whole crossed action recovers each constructed affine map. -/
@[reassoc] theorem firstDividedCrossedAction_affine (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) (a : ((D).X j).affineCover.I₀) :
    ((D).X j).affineCover.f a ≫ firstDividedCrossedAction hπ data hn j hj =
      firstDividedCrossedAffineAction hπ data hn j hj a := by
  rw [firstDividedCrossedAction_def]
  exact ((D).X j).affineCover.ι_glueMorphisms _ _ a

/-- The crossed action contracts to its full normalized divided output. -/
@[reassoc] theorem firstDividedCrossedAction_step (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) :
    firstDividedCrossedAction hπ data hn j hj ≫ finiteGlobalStep hπ data 0 hn =
      (D).f j ≫ pullback.snd _ _ ≫ v := by
  apply ((D).X j).affineCover.hom_ext
  intro a
  rw [firstDividedCrossedAction_affine_assoc, firstDividedCrossedAffineAction_step]

/-- Arbitrary scheme restrictions retain uniqueness of the complete crossed action. -/
theorem firstDividedCrossedAction_unique (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) {T : Scheme.{u}} (p : T ⟶ (D).X j)
    (b : T ⟶ finiteGlobalModel hπ data 1 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstDividedCrossedAction hπ data hn j hj ≫ finiteGlobalStep hπ data 0 hn) :
    b = p ≫ firstDividedCrossedAction hπ data hn j hj :=
  SchemeAffineLiftUniqueness.unique ((D).X j).affineOpenCover
    (firstDividedCrossedAffineAction hπ data hn j hj) (finiteGlobalStep hπ data 0 hn)
    (fun a _ _ t b hb => firstDividedCrossedAffineAction_unique hπ data hn j hj a t b hb)
    (firstDividedCrossedAction hπ data hn j hj) (firstDividedCrossedAction_affine hπ data hn j hj)
    p b hb

/-- The crossed action has exactly the original initial-action output on the full source. -/
@[reassoc] theorem firstDividedCrossedAction_output (j : Option (Option (Fin 3)))
    (hj : j = none ∨ j = some none) :
    firstDividedCrossedAction hπ data hn j hj ≫ finiteGlobalStep hπ data 0 hn =
      (D).f j ≫ pullback.fst _ _ ≫ firstActionOutput hπ data hn := by
  rw [firstDividedCrossedAction_step, ← pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
