/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeAffineLiftUniqueness
public import FLT.Mazur.WeierstrassDividedSuccessorInfinityCenter
public import FLT.Mazur.WeierstrassDividedSuccessorUnitAction

/-!
# The full infinity-input action with normalized divided output

The actual infinity-input affine lifts glue on their entire branch at every
finite successor depth. Uniqueness holds after arbitrary scheme restriction.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (a₀ : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))
  (ha : a₀ ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
    finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)

local notation "v" => finiteNormalizedChart hπ data j hj
local notation "D" => successorDividedInputCover hπ data j hj a₀

/-- The actual affine action on an infinity input with divided output. -/
def successorInfinityInputAffineAction (a : ((D).X none).affineCover.I₀) :
    ((D).X none).affineCover.X a ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  successorDividedUnitAction hπ data j hj a₀ ⟨none, a⟩
    (successorDividedInfinity_center hπ data j hj a₀ a ha)

/-- Each affine infinity-input lift has exactly the prescribed divided output. -/
@[reassoc] theorem successorInfinityInputAffineAction_step (a : ((D).X none).affineCover.I₀) :
    successorInfinityInputAffineAction hπ data j hj a₀ ha a ≫ finiteGlobalStep hπ data j hj =
      ((D).X none).affineCover.f a ≫ (D).f none ≫ pullback.snd _ _ ≫ v := by
  rw [successorInfinityInputAffineAction, successorDividedUnitAction_step]
  exact Category.assoc _ _ _

/-- Every affine restriction of an infinity-input lift is uniquely determined by its step. -/
theorem successorInfinityInputAffineAction_unique (a : ((D).X none).affineCover.I₀)
    {S : Type u} [CommRing S] (p : Spec (.of S) ⟶ ((D).X none).affineCover.X a)
    (b : Spec (.of S) ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorInfinityInputAffineAction hπ data j hj a₀ ha a ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorInfinityInputAffineAction hπ data j hj a₀ ha a :=
  successorDividedUnitAction_affine_unique hπ data j hj a₀ ⟨none, a⟩
    (successorDividedInfinity_center hπ data j hj a₀ a ha) p b hb

/-- The actual infinity-input affine actions agree on their entire scheme intersections. -/
theorem successorInfinityInputAffineAction_overlap (a b : ((D).X none).affineCover.I₀) :
    pullback.fst (((D).X none).affineCover.f a) (((D).X none).affineCover.f b) ≫
        successorInfinityInputAffineAction hπ data j hj a₀ ha a =
      pullback.snd (((D).X none).affineCover.f a) (((D).X none).affineCover.f b) ≫
        successorInfinityInputAffineAction hπ data j hj a₀ ha b :=
  SchemeAffineLiftUniqueness.compatible ((D).X none).affineOpenCover
    (successorInfinityInputAffineAction hπ data j hj a₀ ha) (finiteGlobalStep hπ data j hj)
    ((D).f none ≫ pullback.snd _ _ ≫ v)
    (successorInfinityInputAffineAction_step hπ data j hj a₀ ha)
    (fun a _ _ p b hb => successorInfinityInputAffineAction_unique hπ data j hj a₀ ha a p b hb) a b

/-- The action on the whole infinity-input branch, constructed from its affine lifts. -/
irreducible_def successorInfinityInputAction : (D).X none ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  ((D).X none).affineCover.glueMorphisms (successorInfinityInputAffineAction hπ data j hj a₀ ha)
    (successorInfinityInputAffineAction_overlap hπ data j hj a₀ ha)

/-- Restricting the whole infinity-input action recovers each constructed affine map. -/
@[reassoc] theorem successorInfinityInputAction_affine (a : ((D).X none).affineCover.I₀) :
    ((D).X none).affineCover.f a ≫ successorInfinityInputAction hπ data j hj a₀ ha =
      successorInfinityInputAffineAction hπ data j hj a₀ ha a := by
  rw [successorInfinityInputAction_def]
  exact ((D).X none).affineCover.ι_glueMorphisms _ _ a

/-- The infinity-input action contracts to its full normalized divided output. -/
@[reassoc] theorem successorInfinityInputAction_step :
    successorInfinityInputAction hπ data j hj a₀ ha ≫ finiteGlobalStep hπ data j hj =
      (D).f none ≫ pullback.snd _ _ ≫ v := by
  apply ((D).X none).affineCover.hom_ext
  intro a
  rw [successorInfinityInputAction_affine_assoc, successorInfinityInputAffineAction_step]

/-- Arbitrary scheme restrictions retain uniqueness of the complete infinity-input action. -/
theorem successorInfinityInputAction_unique {T : Scheme.{u}} (p : T ⟶ (D).X none)
    (b : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorInfinityInputAction hπ data j hj a₀ ha ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorInfinityInputAction hπ data j hj a₀ ha :=
  SchemeAffineLiftUniqueness.unique ((D).X none).affineOpenCover
    (successorInfinityInputAffineAction hπ data j hj a₀ ha) (finiteGlobalStep hπ data j hj)
    (fun a _ _ t b hb => successorInfinityInputAffineAction_unique hπ data j hj a₀ ha a t b hb)
    (successorInfinityInputAction hπ data j hj a₀ ha)
    (successorInfinityInputAction_affine hπ data j hj a₀ ha)
    p b hb

/-- The infinity-input action has exactly the preceding-action output on the full source. -/
@[reassoc] theorem successorInfinityInputAction_output :
    successorInfinityInputAction hπ data j hj a₀ ha ≫ finiteGlobalStep hπ data j hj =
      (D).f none ≫ pullback.fst _ _ ≫ successorActionOutput hπ data j hj a₀ := by
  rw [successorInfinityInputAction_step, ← pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
