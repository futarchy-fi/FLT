/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedExteriorCyclicCoordinates
public import FLT.Mazur.EllipticResolvedRetainedCyclicCharts
public import FLT.Mazur.EllipticResolvedTerminalCyclicCharts
public import FLT.Mazur.EllipticResolvedCyclicCoordinateScale

/-!
# Every natural arithmetic label in the original odd closed cycle

The identity, retained branches and terminal branches form one formula for
all original smooth charts. The full Laurent coordinate correction is explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (s : ℕ) (hp : depth = 2 * s + 3)
local notation "F" => ResidueField A
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "data" => splitResolutionData A D
local notation "p" => resolvedSplitStructure A D
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data F
  (a := depth / 2) (b := s + 1) (le_refl _) (by omega) (by omega))
local notation "Z" => zeroSplitCycleComponent hπ data D s (by omega) rfl
  (by omega) (by omega)

/-- Every original arithmetic torus has its explicit scale in the complete odd cyclic model. -/
@[reassoc] theorem resolvedOrientedComponentChart_odd_cyclic (i : Fin depth) :
    resolvedOrientedComponentChart A D r i ≫ (p).smoothLocus.ι ≫ t =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling
        (resolvedCyclicCoordinateScale D r i.val)).toRingHom) ≫
          (PolygonPinching.torusToComponent F).left ≫ (Z ⟨i.val, by omega⟩).left := by
  have he : depth / 2 = s + 1 := by omega
  by_cases h0 : i.val = 0
  · have hi : i = ⟨0, D.depth_pos⟩ := Fin.ext h0
    rw [hi, resolvedCyclicCoordinateScale_zero]
    change _ = Spec.map (CommRingCat.ofHom (PolygonChartScaling.laurent 1)) ≫ _
    rw [PolygonScalingNaturality.laurent_one]
    change _ = Spec.map (𝟙 _) ≫ _
    rw [Spec.map_id, Category.id_comp]
    exact resolvedOrientedComponentChart_odd_zero A D s he r (by omega)
  by_cases hpos : i.val ≤ s
  · let j : Fin s := ⟨i.val - 1, by omega⟩
    have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hi, resolvedCyclicCoordinateScale_positive D r _ (by omega) (by omega)]
    simpa only [Nat.zero_add] using
      resolvedOrientedComponentChart_oddRetainedPositive_cyclic A D r s he j (by omega)
  by_cases ht : i.val = s + 1
  · have hi : i = ⟨depth / 2, by omega⟩ := Fin.ext (show i.val = depth / 2 by omega)
    rw [hi, resolvedCyclicCoordinateScale_positive D r _ (by omega) (by omega)]
    simpa only [he, Nat.zero_add] using
      resolvedOrientedComponentChart_oddPositive_cyclic A D r s he (by omega)
  by_cases hn : i.val = s + 2
  · have hi : i = ⟨depth - depth / 2, by omega⟩ :=
        Fin.ext (show i.val = depth - depth / 2 by omega)
    rw [hi, resolvedCyclicCoordinateScale_negative D r _ (by omega) (by omega)]
    have hlabel : depth - (s + 1) = s + 2 := by omega
    simpa only [he, hlabel, Nat.zero_add] using
      resolvedOrientedComponentChart_oddNegative_cyclic A D r s he (by omega)
  · let j : Fin s := ⟨depth - i.val - 1, by omega⟩
    have hi : i = ⟨depth - (j.val + 1), by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hi, resolvedCyclicCoordinateScale_negative D r _ (by dsimp [j]; omega)
      (by dsimp [j]; omega)]
    simpa only [Nat.zero_add] using
      resolvedOrientedComponentChart_oddRetainedNegative_cyclic A D r s he j hp

end FLT.Mazur.WeierstrassDividedDepth
