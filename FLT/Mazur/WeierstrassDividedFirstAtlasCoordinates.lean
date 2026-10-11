/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstActionAtlas

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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)

local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstDividedAffineCover hπ data hn

/-- The complete affine member's map to the whole action source. -/
def firstDividedSource (i : (U).I₀) : Spec ((U).X i) ⟶
    finiteGlobalActionProduct hπ data 1 hn := (U).f i ≫ pullback.fst _ _

/-- The genuine smooth parameter on each simultaneous affine member. -/
def firstDividedParameter (i : (U).I₀) : Spec ((U).X i) ⟶
    (integralSmoothOpen W).toScheme := firstDividedSource hπ data hn i ≫ pullback.fst _ _

/-- The actual original input, including the retained and infinity branches. -/
def firstDividedOriginalInput (i : (U).I₀) : Spec ((U).X i) ⟶ integralCurve W :=
  firstDividedSource hπ data hn i ≫ pullback.snd _ _ ≫
    finiteGlobalContraction hπ data 1 hn

/-- The parameter and original input have the same coefficient morphism. -/
theorem firstDividedParameter_structure (i : (U).I₀) :
    firstDividedParameter hπ data hn i ≫ integralSmoothStructure W =
      firstDividedOriginalInput hπ data hn i ≫ integralCurveStructure W := by
  simp only [firstDividedParameter, firstDividedOriginalInput, Category.assoc]
  exact congrArg (fun t => firstDividedSource hπ data hn i ≫ t) pullback.condition

/-- The original input factors through its actual successor input-chart projection. -/
@[reassoc] theorem firstDividedInputProjection_original (i : (U).I₀) :
    firstDividedInputProjection hπ data hn i ≫
        finiteSuccessiveAtlasMap hπ data 0 hn (firstDividedInputIndex hπ data hn i) ≫
          finiteGlobalContraction hπ data 1 hn = firstDividedOriginalInput hπ data hn i := by
  simpa only [firstDividedOriginalInput, firstDividedSource, firstDividedOutputInput,
    Category.assoc] using firstDividedInputProjection_input_assoc hπ data hn i
      (finiteGlobalContraction hπ data 1 hn)

/-- The actual normalized output coordinates on every affine member. -/
def firstDividedAlpha (i : (U).I₀) : B →+* (U).X i :=
  affineChartRingHom ((U).f i ≫ pullback.snd _ _)

/-- Extracting coordinates keeps the complete normalized output map. -/
@[simp] theorem firstDividedAlpha_spec (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom (firstDividedAlpha hπ data hn i)) =
      (U).f i ≫ pullback.snd _ _ := affineChartRingHom_spec _

/-- The normalized output contracts to the action on the actual original input. -/
theorem firstDividedAlpha_addition (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom ((firstDividedAlpha hπ data hn i).comp
        (q).toRingHom)) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W (firstDividedParameter hπ data hn i)
        (firstDividedOriginalInput hπ data hn i)
        (firstDividedParameter_structure hπ data hn i) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, firstDividedAlpha_spec,
    Category.assoc, ← finiteNormalizedChart_contraction hπ data 0 hn,
    ← pullback.condition_assoc, firstActionOutput_contraction]
  unfold leftSmoothPointAddition
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteGlobalActionInput_fst, pullback.lift_fst,
      firstDividedParameter, firstDividedSource]
  · simp only [Category.assoc, finiteGlobalActionInput_snd, pullback.lift_snd,
      firstDividedOriginalInput, firstDividedSource]

end FLT.Mazur.WeierstrassDividedDepth
