/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstActionInput
public import FLT.Mazur.WeierstrassDividedGlobalSuccessiveCover
public import FLT.Mazur.WeierstrassModifiedSmoothAffineRefinement

/-!
# The full simultaneous first-successor atlas over divided outputs

All first-successor input charts are pulled back to the divided-output
domain of the existing initial action. Affine refinement covers the entire
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)

local notation "v" => finiteNormalizedChart hπ data 0 hn

/-- The entire first-successor source whose existing initial action has divided output. -/
abbrev firstDividedOutputDomain := pullback (firstActionOutput hπ data hn) v

/-- Retain the whole successor input on the divided-output domain. -/
def firstDividedOutputInput : firstDividedOutputDomain hπ data hn ⟶
    finiteGlobalModel hπ data 1 hn := pullback.fst _ _ ≫ pullback.snd _ _

/-- The full input projection is flat, including points above the exceptional fiber. -/
instance firstDividedOutputInput_flat : Flat (firstDividedOutputInput hπ data hn) := by
  unfold firstDividedOutputInput
  infer_instance

/-- Pull back every retained and fraction input chart to the divided-output domain. -/
def firstDividedInputCover : (firstDividedOutputDomain hπ data hn).OpenCover :=
  (finiteSuccessiveOpenCover hπ data 0 hn).pullback₁ (firstDividedOutputInput hπ data hn)

/-- The simultaneous affine atlas covers every input with divided output. -/
def firstDividedAffineCover : (firstDividedOutputDomain hπ data hn).AffineOpenCover :=
  (firstDividedInputCover hπ data hn).affineRefinement

/-- The original input chart assigned to each actual affine presentation. -/
def firstDividedInputIndex (i : (firstDividedAffineCover hπ data hn).I₀) :
    Option (Option (Fin 3)) := i.1

/-- Each affine member retains its actual input-chart projection. -/
def firstDividedInputProjection (i : (firstDividedAffineCover hπ data hn).I₀) :
    Spec ((firstDividedAffineCover hπ data hn).X i) ⟶
      finiteSuccessiveAtlasObject hπ data 0 hn (firstDividedInputIndex hπ data hn i) :=
  ((firstDividedInputCover hπ data hn).X i.1).affineCover.f i.2 ≫ pullback.snd _ _

/-- The actual input-chart projections on the simultaneous atlas are flat. -/
instance firstDividedInputProjection_flat (i : (firstDividedAffineCover hπ data hn).I₀) :
    Flat (firstDividedInputProjection hπ data hn i) := by
  unfold firstDividedInputProjection
  infer_instance

/-- Each input projection agrees with the entire first-successor input. -/
@[reassoc] theorem firstDividedInputProjection_input
    (i : (firstDividedAffineCover hπ data hn).I₀) :
    firstDividedInputProjection hπ data hn i ≫
        finiteSuccessiveAtlasMap hπ data 0 hn (firstDividedInputIndex hπ data hn i) =
      (firstDividedAffineCover hπ data hn).f i ≫ firstDividedOutputInput hπ data hn := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => ((firstDividedInputCover hπ data hn).X i.1).affineCover.f i.2 ≫ t)
      (pullback.condition (f := firstDividedOutputInput hπ data hn)
        (g := (finiteSuccessiveOpenCover hπ data 0 hn).f i.1)).symm).trans
          (Category.assoc _ _ _).symm)

/-- No input point over the actual divided output is omitted. -/
theorem firstDividedAffineCover_covers (z : firstDividedOutputDomain hπ data hn) :
    ∃ i x, (firstDividedAffineCover hπ data hn).f i x = z :=
  (firstDividedAffineCover hπ data hn).openCover.exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
