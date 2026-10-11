/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorExteriorAtlas

/-!
# Original-action coordinates on the refined retained-input atlas

Every original or successive retained x chart keeps its full original
input map. Its normalized output is the genuine original smooth addition,
with the coefficient morphism fixed by the actual source product.
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
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e)
local notation "D" => successorDividedInputCover hπ data j hj a
local notation "U" => successorRetainedAffineCover hπ data j hj a

/-- The retained affine member's actual map to the whole source product. -/
def successorRetainedSource (i : (U).I₀) : Spec ((U).X i) ⟶
    finiteGlobalActionProduct hπ data (j + 1) hj :=
  (U).f i ≫ (D).f (some none) ≫ pullback.fst _ _

/-- The genuine smooth parameter of the refined retained member. -/
def successorRetainedParameter (i : (U).I₀) : Spec ((U).X i) ⟶
    (integralSmoothOpen W).toScheme :=
  successorRetainedSource hπ data j hj a i ≫ pullback.fst _ _

/-- The actual original cubic input of the refined retained member. -/
def successorRetainedOriginalInput (i : (U).I₀) : Spec ((U).X i) ⟶ integralCurve W :=
  successorRetainedSource hπ data j hj a i ≫ pullback.snd _ _ ≫
    finiteGlobalContraction hπ data (j + 1) hj

/-- The parameter and input retain the same coefficient morphism. -/
theorem successorRetainedParameter_structure (i : (U).I₀) :
    successorRetainedParameter hπ data j hj a i ≫ integralSmoothStructure W =
      successorRetainedOriginalInput hπ data j hj a i ≫ integralCurveStructure W := by
  simp only [successorRetainedParameter, successorRetainedOriginalInput, Category.assoc]
  exact congrArg (fun t => successorRetainedSource hπ data j hj a i ≫ t) pullback.condition

/-- Refinement preserves the original map of the actual retained equation chart. -/
@[reassoc] theorem successorRetainedChartProjection_original (i : (U).I₀) :
    successorRetainedChartProjection hπ data j hj a i ≫
        finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) i.1 ≫
          finitePrecedingExteriorChart hπ data j hj ≫
            finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
      successorRetainedOriginalInput hπ data j hj a i := by
  rw [successorRetainedChartProjection_input_assoc,
    ← finiteSuccessiveRetainedChart_step_assoc, finiteGlobalStep_contraction]
  unfold successorRetainedInputProjection
  have h := pullback.condition (f := successorDividedOutputInput hπ data j hj a)
    (g := (finiteSuccessiveOpenCover hπ data j hj).f (some none))
  change pullback.fst _ _ ≫ successorDividedOutputInput hπ data j hj a =
    pullback.snd _ _ ≫ finiteSuccessiveRetainedChart hπ data j hj at h
  rw [← Category.assoc (pullback.snd _ _), ← h]
  simp only [successorRetainedOriginalInput, successorRetainedSource,
    successorDividedOutputInput, Category.assoc]
  rfl

/-- The normalized output coordinates on every retained equation-chart refinement. -/
def successorRetainedAlpha (i : (U).I₀) : B →+* (U).X i :=
  affineChartRingHom ((U).f i ≫ (D).f (some none) ≫ pullback.snd _ _)

/-- These ring coordinates retain the exact normalized output morphism. -/
@[simp] theorem successorRetainedAlpha_spec (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom (successorRetainedAlpha hπ data j hj a i)) =
      (U).f i ≫ (D).f (some none) ≫ pullback.snd _ _ := affineChartRingHom_spec _

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
include ha

/-- Every refined retained output is the original smooth addition on its actual input. -/
theorem successorRetainedAlpha_addition (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom ((successorRetainedAlpha hπ data j hj a i).comp
        (previousOriginalMap hπ d e).toRingHom)) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W (successorRetainedParameter hπ data j hj a i)
        (successorRetainedOriginalInput hπ data j hj a i)
        (successorRetainedParameter_structure hπ data j hj a i) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, successorRetainedAlpha_spec,
    Category.assoc, Category.assoc, ← finiteNormalizedChart_contraction hπ data j hj,
    ← pullback.condition_assoc, successorActionOutput_contraction hπ data j hj a ha]
  unfold leftSmoothPointAddition
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteGlobalActionInput_fst, pullback.lift_fst,
      successorRetainedParameter, successorRetainedSource]
  · simp only [Category.assoc, finiteGlobalActionInput_snd, pullback.lift_snd,
      successorRetainedOriginalInput, successorRetainedSource]

end FLT.Mazur.WeierstrassDividedDepth
