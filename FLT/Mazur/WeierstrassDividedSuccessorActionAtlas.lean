/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorActionInput
public import FLT.Mazur.WeierstrassDividedGlobalSuccessiveCover
public import FLT.Mazur.WeierstrassModifiedSmoothAffineRefinement

/-!
# The full simultaneous successor atlas over divided outputs

All successor input charts are pulled back to the divided-output
domain of the preceding action. Affine refinement covers the entire
domain, including retained exterior and infinity inputs. Each input
projection is flat, proved by smooth base change and open restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))

local notation "v" => finiteNormalizedChart hπ data j hj

/-- The entire successor source whose preceding action has divided output. -/
abbrev successorDividedOutputDomain := pullback (successorActionOutput hπ data j hj a) v

/-- Retain the whole successor input on the divided-output domain. -/
def successorDividedOutputInput : successorDividedOutputDomain hπ data j hj a ⟶
    finiteGlobalModel hπ data (j + 1) hj := pullback.fst _ _ ≫ pullback.snd _ _

/-- The full input projection is flat, including points above the exceptional fiber. -/
instance successorDividedOutputInput_flat : Flat (successorDividedOutputInput hπ data j hj a) := by
  unfold successorDividedOutputInput
  infer_instance

/-- Pull back every retained and fraction input chart to the divided-output domain. -/
def successorDividedInputCover : (successorDividedOutputDomain hπ data j hj a).OpenCover :=
  (finiteSuccessiveOpenCover hπ data j hj).pullback₁ (successorDividedOutputInput hπ data j hj a)

/-- The simultaneous affine atlas covers every input with divided output. -/
def successorDividedAffineCover : (successorDividedOutputDomain hπ data j hj a).AffineOpenCover :=
  (successorDividedInputCover hπ data j hj a).affineRefinement

/-- The original input chart assigned to each actual affine presentation. -/
def successorDividedInputIndex (i : (successorDividedAffineCover hπ data j hj a).I₀) :
    Option (Option (Fin 3)) := i.1

/-- Each affine member retains its actual input-chart projection. -/
def successorDividedInputProjection (i : (successorDividedAffineCover hπ data j hj a).I₀) :
    Spec ((successorDividedAffineCover hπ data j hj a).X i) ⟶
      finiteSuccessiveAtlasObject hπ data j hj (successorDividedInputIndex hπ data j hj a i) :=
  ((successorDividedInputCover hπ data j hj a).X i.1).affineCover.f i.2 ≫ pullback.snd _ _

/-- The actual input-chart projections on the simultaneous atlas are flat. -/
instance successorDividedInputProjection_flat
    (i : (successorDividedAffineCover hπ data j hj a).I₀) :
    Flat (successorDividedInputProjection hπ data j hj a i) := by
  unfold successorDividedInputProjection
  infer_instance

/-- Each input projection agrees with the entire successor input. -/
@[reassoc] theorem successorDividedInputProjection_input
    (i : (successorDividedAffineCover hπ data j hj a).I₀) :
    successorDividedInputProjection hπ data j hj a i ≫
        finiteSuccessiveAtlasMap hπ data j hj (successorDividedInputIndex hπ data j hj a i) =
      (successorDividedAffineCover hπ data j hj a).f i ≫
        successorDividedOutputInput hπ data j hj a := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => ((successorDividedInputCover hπ data j hj a).X i.1).affineCover.f i.2 ≫ t)
      (pullback.condition (f := successorDividedOutputInput hπ data j hj a)
        (g := (finiteSuccessiveOpenCover hπ data j hj).f i.1)).symm).trans
          (Category.assoc _ _ _).symm)

/-- No input point over the actual divided output is omitted. -/
theorem successorDividedAffineCover_covers (z : successorDividedOutputDomain hπ data j hj a) :
    ∃ i x, (successorDividedAffineCover hπ data j hj a).f i x = z :=
  (successorDividedAffineCover hπ data j hj a).openCover.exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
