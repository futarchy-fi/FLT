/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeAffineFlatLiftGluing
public import FLT.Mazur.WeierstrassDividedSuccessorFractionAction

/-!
# Whole successor fraction-input actions at arbitrary depth

The actual affine lifts glue on every full fraction-input branch.
Uniqueness persists under flat restriction by an arbitrary scheme.
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

variable (t : Fin 3)

local notation "v" => finiteNormalizedChart hπ data j hj
local notation "D" => successorDividedInputCover hπ data j hj a₀

/-- The actual fraction-input affine actions agree on their entire scheme intersections. -/
theorem successorFractionInputAffineAction_overlap (a b : ((D).X (some (some t))).affineCover.I₀) :
    pullback.fst (((D).X (some (some t))).affineCover.f a)
        (((D).X (some (some t))).affineCover.f b) ≫
        successorFractionAffineAction hπ data j hj a₀ t a ha =
      pullback.snd (((D).X (some (some t))).affineCover.f a)
          (((D).X (some (some t))).affineCover.f b) ≫
        successorFractionAffineAction hπ data j hj a₀ t b ha :=
  SchemeAffineFlatLiftGluing.compatible ((D).X (some (some t))).affineOpenCover
    (fun z => successorFractionAffineAction hπ data j hj a₀ t z ha) (finiteGlobalStep hπ data j hj)
    ((D).f (some (some t)) ≫ pullback.snd _ _ ≫ v)
    (fun z => by
      rw [successorFractionAffineAction_step]
      exact Category.assoc _ _ _)
    (fun z _ _ p _ b hb =>
      successorFractionAffineAction_flat_unique hπ data j hj a₀ t z ha p b hb) a b

/-- The action on the whole fraction-input branch, constructed from its affine lifts. -/
irreducible_def successorFractionInputAction :
    (D).X (some (some t)) ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  ((D).X (some (some t))).affineCover.glueMorphisms
    (fun z => successorFractionAffineAction hπ data j hj a₀ t z ha)
    (successorFractionInputAffineAction_overlap hπ data j hj a₀ ha t)

/-- Restricting the whole fraction-input action recovers each constructed affine map. -/
@[reassoc] theorem successorFractionInputAction_affine
    (a : ((D).X (some (some t))).affineCover.I₀) :
    ((D).X (some (some t))).affineCover.f a ≫ successorFractionInputAction hπ data j hj a₀ ha t =
      successorFractionAffineAction hπ data j hj a₀ t a ha := by
  rw [successorFractionInputAction_def]
  exact ((D).X (some (some t))).affineCover.ι_glueMorphisms _ _ a

/-- The fraction-input action contracts to its full normalized divided output. -/
@[reassoc] theorem successorFractionInputAction_step :
    successorFractionInputAction hπ data j hj a₀ ha t ≫ finiteGlobalStep hπ data j hj =
      (D).f (some (some t)) ≫ pullback.snd _ _ ≫ v := by
  apply ((D).X (some (some t))).affineCover.hom_ext
  intro a
  rw [successorFractionInputAction_affine_assoc, successorFractionAffineAction_step]
  exact Category.assoc _ _ _

/-- Flat scheme restrictions retain uniqueness of the complete fraction-input action. -/
theorem successorFractionInputAction_flat_unique {T : Scheme.{u}}
    (p : T ⟶ (D).X (some (some t))) [Flat p]
    (b : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorFractionInputAction hπ data j hj a₀ ha t ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorFractionInputAction hπ data j hj a₀ ha t :=
  SchemeAffineFlatLiftGluing.flat_unique ((D).X (some (some t))).affineOpenCover
    (fun z => successorFractionAffineAction hπ data j hj a₀ t z ha) (finiteGlobalStep hπ data j hj)
    (fun z _ _ p _ b hb =>
      successorFractionAffineAction_flat_unique hπ data j hj a₀ t z ha p b hb)
    (successorFractionInputAction hπ data j hj a₀ ha t)
    (successorFractionInputAction_affine hπ data j hj a₀ ha t)
    p b hb

/-- The fraction-input action has exactly the preceding-action output on the full source. -/
@[reassoc] theorem successorFractionInputAction_output :
    successorFractionInputAction hπ data j hj a₀ ha t ≫ finiteGlobalStep hπ data j hj =
      (D).f (some (some t)) ≫ pullback.fst _ _ ≫ successorActionOutput hπ data j hj a₀ := by
  rw [successorFractionInputAction_step, ← pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
