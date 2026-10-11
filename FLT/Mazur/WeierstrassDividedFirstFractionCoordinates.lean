/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionDomain

/-!
# Original-action equations on actual successor presentations

The simultaneous affine atlas supplies both divided ring maps and the
smooth parameter. Its equations identify the actual original action,
rather than postulating a lift on a new test ring.
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
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + 0))
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b3)
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b4)
    (π ^ 2 * (data ⟨1, Nat.lt_succ_of_le hn⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b3
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b4
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b6)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "C" => BlowupFractionChart.chart I f
local notation "c" => finiteSuccessiveFractionChart hπ data 0 hn f hf
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstFractionCover hπ data hn f hf

/-- The actual input divided coordinates factor through the fraction projection. -/
def firstFractionBeta (i : (U).I₀) : B →+* (U).X i :=
  (firstFractionHom hπ data hn f hf i).comp (algebraMap B C)

/-- The actual output divided coordinates, extracted from the pullback projection. -/
def firstFractionAlpha (i : (U).I₀) : B →+* (U).X i :=
  affineChartRingHom (firstFractionDividedOutput hπ data hn f hf i)

/-- The output coordinates retain exactly the divided projection. -/
@[simp] theorem firstFractionAlpha_spec (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom (firstFractionAlpha hπ data hn f hf i)) =
      firstFractionDividedOutput hπ data hn f hf i := affineChartRingHom_spec _

/-- The input coordinates retain exactly the actual first successor contraction. -/
@[reassoc] theorem firstFractionBeta_original (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom ((firstFractionBeta hπ data hn f hf i).comp
        (q).toRingHom)) ≫ integralCurveChart W 2 =
      firstFractionProjection hπ data hn f hf i ≫ c ≫
        finiteGlobalContraction hπ data 1 hn := by
  rw [firstFractionBeta, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    firstFractionHom_spec, finiteSuccessiveFractionChart_contraction]

/-- The actual parameter and the original input agree over the coefficient scheme. -/
theorem firstFractionParameter_original_structure (i : (U).I₀) :
    firstFractionParameter hπ data hn f hf i ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom ((firstFractionBeta hπ data hn f hf i).comp
        (q).toRingHom)) ≫ integralCurveChart W 2) ≫ integralCurveStructure W := by
  rw [firstFractionBeta_original]
  simp only [firstFractionParameter, firstFractionProjection, Category.assoc]
  exact congrArg (fun t => (U).f i ≫ pullback.fst _ _ ≫ t) pullback.condition

/-- Divided output coordinates present the existing original action on the actual input. -/
theorem firstFractionAlpha_original_addition (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom ((firstFractionAlpha hπ data hn f hf i).comp
        (q).toRingHom)) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W (firstFractionParameter hπ data hn f hf i)
        (Spec.map (CommRingCat.ofHom ((firstFractionBeta hπ data hn f hf i).comp
          (q).toRingHom)) ≫ integralCurveChart W 2)
        (firstFractionParameter_original_structure hπ data hn f hf i) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, firstFractionAlpha_spec,
    ← finiteNormalizedChart_contraction hπ data 0 hn]
  simp only [firstFractionDividedOutput, Category.assoc]
  rw [← pullback.condition_assoc]
  simp only [firstFractionOutput, Category.assoc, firstActionOutput_contraction]
  simp only [firstFractionBeta_original]
  unfold leftSmoothPointAddition
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteGlobalActionInput_fst,
      firstFractionInput, pullback.lift_fst, firstFractionParameter, firstFractionOutput]
  · simp only [Category.assoc, finiteGlobalActionInput_snd,
      firstFractionInput, pullback.lift_snd, firstFractionProjection, pullback.lift_snd_assoc,
      firstFractionOutput]

end FLT.Mazur.WeierstrassDividedDepth
