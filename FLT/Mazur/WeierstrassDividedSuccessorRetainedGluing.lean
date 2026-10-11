/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeAffineLiftUniqueness
public import FLT.Mazur.WeierstrassDividedSuccessorRetainedAction

/-!
# The full retained-input successor action at arbitrary depth

All original and successive x-chart lifts glue on the entire retained
branch. Their uniqueness persists after arbitrary scheme restriction,
including restrictions that are not flat over an equation chart.
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
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))
  (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
    finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
local notation "U" => successorRetainedAffineCover hπ data j hj a
local notation "D" => successorDividedInputCover hπ data j hj a
local notation "v" => finiteNormalizedChart hπ data j hj

/-- Actual retained affine lifts agree on all scheme intersections. -/
theorem successorRetainedAffineAction_overlap (i k : (U).I₀) :
    pullback.fst ((U).f i) ((U).f k) ≫ successorRetainedAffineAction hπ data j hj a ha i =
      pullback.snd ((U).f i) ((U).f k) ≫ successorRetainedAffineAction hπ data j hj a ha k :=
  SchemeAffineLiftUniqueness.compatible U (successorRetainedAffineAction hπ data j hj a ha)
    (finiteGlobalStep hπ data j hj) ((D).f (some none) ≫ pullback.snd _ _ ≫ v)
    (successorRetainedAffineAction_step hπ data j hj a ha)
    (fun i _ _ p b hb => successorRetainedAffineAction_affine_unique hπ data j hj a ha i p b hb)
    i k

/-- The actual action on the whole retained-input branch of the successor source. -/
irreducible_def successorRetainedAction :
    successorRetainedInputDomain hπ data j hj a ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  (U).openCover.glueMorphisms (successorRetainedAffineAction hπ data j hj a ha)
    (successorRetainedAffineAction_overlap hπ data j hj a ha)

/-- Restriction to every original or successive retained member recovers its affine lift. -/
@[reassoc] theorem successorRetainedAction_affine (i : (U).I₀) :
    (U).f i ≫ successorRetainedAction hπ data j hj a ha =
      successorRetainedAffineAction hπ data j hj a ha i := by
  rw [successorRetainedAction_def]
  exact (U).openCover.ι_glueMorphisms _ _ i

/-- The complete retained action has exactly the prescribed normalized output. -/
@[reassoc] theorem successorRetainedAction_step :
    successorRetainedAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj =
      (D).f (some none) ≫ pullback.snd _ _ ≫ v := by
  apply (U).openCover.hom_ext
  intro i
  exact (successorRetainedAction_affine_assoc hπ data j hj a ha i _).trans
    (successorRetainedAffineAction_step hπ data j hj a ha i)

/-- Every scheme restriction of the complete retained action is uniquely determined by its step. -/
theorem successorRetainedAction_unique {T : Scheme.{u}}
    (p : T ⟶ successorRetainedInputDomain hπ data j hj a)
    (b : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorRetainedAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorRetainedAction hπ data j hj a ha :=
  SchemeAffineLiftUniqueness.unique U (successorRetainedAffineAction hπ data j hj a ha)
    (finiteGlobalStep hπ data j hj)
    (fun i _ _ t b hb => successorRetainedAffineAction_affine_unique hπ data j hj a ha i t b hb)
    (successorRetainedAction hπ data j hj a ha) (successorRetainedAction_affine hπ data j hj a ha)
    p b hb

/-- The whole retained lift contracts to the preceding action on its entire domain. -/
@[reassoc] theorem successorRetainedAction_output :
    successorRetainedAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj =
      (D).f (some none) ≫ pullback.fst _ _ ≫ successorActionOutput hπ data j hj a := by
  rw [successorRetainedAction_step, ← pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
