/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothAction

/-!
# The actual input product for an integral action on a finite modification

The product retains the original smooth parameter and the entire original finite
model. Its contraction is an actual pair on the whole cubic. The embedded smooth
pair retains both original inputs, with no assumed modification action.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassDividedDepth

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- The smooth parameter times the whole actual finite model over the original base. -/
abbrev finiteGlobalActionProduct :=
  pullback (integralSmoothStructure W) (finiteGlobalStructure hπ data j hj)

/-- Contract the second input, retaining the actual smooth parameter. -/
def finiteGlobalActionInput :
    finiteGlobalActionProduct hπ data j hj ⟶ leftSmoothFactorProduct W :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ finiteGlobalContraction hπ data j hj)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The contraction of inputs fixes the original smooth parameter. -/
@[reassoc] theorem finiteGlobalActionInput_fst :
    finiteGlobalActionInput hπ data j hj ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The other input is precisely the original finite contraction. -/
@[reassoc] theorem finiteGlobalActionInput_snd :
    finiteGlobalActionInput hπ data j hj ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finiteGlobalContraction hπ data j hj := pullback.lift_snd _ _ _

/-- The original smooth pair sits in the product with the whole finite model. -/
def finiteGlobalOriginalSmoothPair :
    smoothFactorProduct W ⟶ finiteGlobalActionProduct hπ data j hj :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ finiteGlobalSmoothEmbedding hπ data j hj)
    (by rw [Category.assoc, finiteGlobalSmoothEmbedding_structure]; exact pullback.condition)

/-- The smooth pair retains its original first input. -/
@[reassoc] theorem finiteGlobalOriginalSmoothPair_fst :
    finiteGlobalOriginalSmoothPair hπ data j hj ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The smooth pair uses the actual original smooth embedding for its second input. -/
@[reassoc] theorem finiteGlobalOriginalSmoothPair_snd :
    finiteGlobalOriginalSmoothPair hπ data j hj ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finiteGlobalSmoothEmbedding hπ data j hj := pullback.lift_snd _ _ _

/-- The original smooth input diagram commutes with the entire finite contraction. -/
@[reassoc] theorem finiteGlobalOriginalSmoothPair_input :
    finiteGlobalOriginalSmoothPair hπ data j hj ≫ finiteGlobalActionInput hπ data j hj =
      smoothFactorsToLeftSmooth W := by
  apply pullback.hom_ext
  · rw [Category.assoc, finiteGlobalActionInput_fst, finiteGlobalOriginalSmoothPair_fst,
      smoothFactorsToLeftSmooth_fst]
  · rw [Category.assoc, finiteGlobalActionInput_snd,
      finiteGlobalOriginalSmoothPair_snd_assoc, finiteGlobalSmoothEmbedding_contraction,
      smoothFactorsToLeftSmooth_snd]

/-- Contracting the lifted smooth-open action gives the actual contracted input action. -/
theorem finiteGlobalOriginalSmoothAction_input :
    finiteGlobalOriginalSmoothAction hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      finiteGlobalOriginalSmoothPair hπ data j hj ≫ finiteGlobalActionInput hπ data j hj ≫
        leftSmoothFactorAddition W := by
  rw [finiteGlobalOriginalSmoothPair_input_assoc, finiteGlobalOriginalSmoothAction_contraction]

end FLT.Mazur.WeierstrassDividedDepth
