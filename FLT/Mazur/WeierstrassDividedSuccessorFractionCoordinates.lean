/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorAtlasCoordinates

/-!
# Actual fraction-input coordinates at every finite successor

The complete simultaneous atlas supplies flat presentations of all three
successive fraction charts. Their divided coordinates retain the exact
original input and genuine smooth addition, including exceptional points.
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
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "g" => WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "hg" => WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "q" => previousOriginalMap hπ d e
local notation "U" => successorDividedAffineCover hπ data j hj a
local notation "D" => successorDividedInputCover hπ data j hj a
variable (t : Fin 3) (z : ((successorDividedInputCover hπ data j hj a).X
  (some (some t))).affineCover.I₀)
local notation "i" => Sigma.mk (some (some t)) z
local notation "C" => BlowupFractionChart.chart I (g t)

/-- Extract the actual fraction-input ring presentation on each affine member. -/
def successorFractionHom : C →+* (U).X i :=
  affineChartRingHom (successorDividedInputProjection hπ data j hj a i)

/-- The fraction presentation is precisely the actual input projection. -/
@[simp] theorem successorFractionHom_spec :
    Spec.map (CommRingCat.ofHom (successorFractionHom hπ data j hj a t z)) =
      successorDividedInputProjection hπ data j hj a i := affineChartRingHom_spec _

/-- Fraction-presentation flatness follows from the actual simultaneous input atlas. -/
theorem successorFractionHom_flat : RingHom.Flat (successorFractionHom hπ data j hj a t z) := by
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
    (successorFractionHom hπ data j hj a t z))).mp
  rw [successorFractionHom_spec]
  exact successorDividedInputProjection_flat hπ data j hj a i

/-- The normalized divided input coordinates factor through the genuine fraction algebra. -/
def successorFractionBeta : B →+* (U).X i :=
  (successorFractionHom hπ data j hj a t z).comp (algebraMap B C)

/-- The fraction coordinates retain the original input on the entire successor source. -/
@[reassoc] theorem successorFractionBeta_original :
    Spec.map (CommRingCat.ofHom ((successorFractionBeta hπ data j hj a t z).comp
        (q).toRingHom)) ≫ integralCurveChart W 2 =
      successorDividedOriginalInput hπ data j hj a i := by
  rw [successorFractionBeta, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    CommRingCat.ofHom_comp, Spec.map_comp, successorFractionHom_spec, Category.assoc]
  have he := successorDividedInputProjection_original hπ data j hj a i
  change successorDividedInputProjection hπ data j hj a i ≫
    finiteSuccessiveFractionChart hπ data j hj (g t) (hg t) ≫
      finiteGlobalContraction hπ data (j + 1) hj = _ at he
  rwa [finiteSuccessiveFractionChart_contraction] at he

/-- The smooth parameter and extracted fraction coordinates preserve the same base morphism. -/
theorem successorFractionParameter_structure :
    successorDividedParameter hπ data j hj a i ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom ((successorFractionBeta hπ data j hj a t z).comp
        (q).toRingHom)) ≫ integralCurveChart W 2) ≫ integralCurveStructure W := by
  rw [successorFractionBeta_original]
  exact successorDividedParameter_structure hπ data j hj a i

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
include ha

/-- Every actual fraction input has the prescribed original smooth addition as output. -/
theorem successorFractionAlpha_addition :
    Spec.map (CommRingCat.ofHom ((successorDividedAlpha hπ data j hj a i).comp
        (q).toRingHom)) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W (successorDividedParameter hπ data j hj a i)
        (Spec.map (CommRingCat.ofHom ((successorFractionBeta hπ data j hj a t z).comp
          (q).toRingHom)) ≫ integralCurveChart W 2)
        (successorFractionParameter_structure hπ data j hj a t z) := by
  simpa only [successorFractionBeta_original] using
    successorDividedAlpha_addition hπ data j hj a ha i

end FLT.Mazur.WeierstrassDividedDepth
