/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorActionAtlas

/-!
# Original-action coordinates on the complete divided-output atlas

Every input branch retains its actual smooth parameter, original input,
and normalized output. These identities include both crossed retained cases.
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

local notation "v" => finiteNormalizedChart hπ data j hj

local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => successorDividedAffineCover hπ data j hj a

/-- The complete affine member's map to the whole action source. -/
def successorDividedSource (i : (U).I₀) : Spec ((U).X i) ⟶
    finiteGlobalActionProduct hπ data (j + 1) hj := (U).f i ≫ pullback.fst _ _

/-- The genuine smooth parameter on each simultaneous affine member. -/
def successorDividedParameter (i : (U).I₀) : Spec ((U).X i) ⟶
    (integralSmoothOpen W).toScheme := successorDividedSource hπ data j hj a i ≫ pullback.fst _ _

/-- The actual original input, including the retained and infinity branches. -/
def successorDividedOriginalInput (i : (U).I₀) : Spec ((U).X i) ⟶ integralCurve W :=
  successorDividedSource hπ data j hj a i ≫ pullback.snd _ _ ≫
    finiteGlobalContraction hπ data (j + 1) hj

/-- The parameter and original input have the same coefficient morphism. -/
theorem successorDividedParameter_structure (i : (U).I₀) :
    successorDividedParameter hπ data j hj a i ≫ integralSmoothStructure W =
      successorDividedOriginalInput hπ data j hj a i ≫ integralCurveStructure W := by
  simp only [successorDividedParameter, successorDividedOriginalInput, Category.assoc]
  exact congrArg (fun t => successorDividedSource hπ data j hj a i ≫ t) pullback.condition

/-- The original input factors through its actual successor input-chart projection. -/
@[reassoc] theorem successorDividedInputProjection_original (i : (U).I₀) :
    successorDividedInputProjection hπ data j hj a i ≫
        finiteSuccessiveAtlasMap hπ data j hj (successorDividedInputIndex hπ data j hj a i) ≫
          finiteGlobalContraction hπ data (j + 1) hj =
      successorDividedOriginalInput hπ data j hj a i := by
  simpa only [successorDividedOriginalInput, successorDividedSource, successorDividedOutputInput,
    Category.assoc] using successorDividedInputProjection_input_assoc hπ data j hj a i
      (finiteGlobalContraction hπ data (j + 1) hj)

/-- The actual normalized output coordinates on every affine member. -/
def successorDividedAlpha (i : (U).I₀) : B →+* (U).X i :=
  affineChartRingHom ((U).f i ≫ pullback.snd _ _)

/-- Extracting coordinates keeps the complete normalized output map. -/
@[simp] theorem successorDividedAlpha_spec (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom (successorDividedAlpha hπ data j hj a i)) =
      (U).f i ≫ pullback.snd _ _ := affineChartRingHom_spec _

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
include ha

/-- The normalized output contracts to the action on the actual original input. -/
theorem successorDividedAlpha_addition (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom ((successorDividedAlpha hπ data j hj a i).comp
        (q).toRingHom)) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W (successorDividedParameter hπ data j hj a i)
        (successorDividedOriginalInput hπ data j hj a i)
        (successorDividedParameter_structure hπ data j hj a i) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, successorDividedAlpha_spec,
    Category.assoc, ← finiteNormalizedChart_contraction hπ data j hj,
    ← pullback.condition_assoc, successorActionOutput_contraction hπ data j hj a ha]
  unfold leftSmoothPointAddition
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteGlobalActionInput_fst, pullback.lift_fst,
      successorDividedParameter, successorDividedSource]
  · simp only [Category.assoc, finiteGlobalActionInput_snd, pullback.lift_snd,
      successorDividedOriginalInput, successorDividedSource]

end FLT.Mazur.WeierstrassDividedDepth
