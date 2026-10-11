/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup
public import FLT.Mazur.WeierstrassDividedInfinityLaurentChart
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup
import all FLT.Mazur.WeierstrassDividedPositiveEqualityCycleEndCharts

/-!
# The smooth exterior component retains the actual cubic contraction

The original infinity Laurent parameter is the reciprocal of the cyclic
smooth coordinate. The full chart and every original cubic function survive.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveEqualityCycleNodes hπ data D s hs hstart hk
local notation "E" => initialExteriorOrientedIso hπ data D (s + 1) hs hstart
  (by omega) (by omega)
local notation "L" => infinityLaurentChart hπ data D (by omega) (s + 1) hs
local notation "M" => Over.Hom.left (PolygonSplitGroup.component K (2 * s + 4) 0 ≫
  positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp)

/-- The cyclic exterior's reciprocal torus is the entire original infinity Laurent chart. -/
@[reassoc] theorem positiveEqualityCycleComponent_exterior_laurent :
    ProjectiveLine.overlapRight K ≫ ProjectiveLine.left K ≫ (Z 0).left = L := by
  rw [← initialExteriorOrientedIso_laurent_assoc hπ data D (s + 1) hs hstart
    (by omega) (by omega)]
  simp only [initialExteriorLaurentChart, Category.assoc]
  rw [positiveEqualityCycleComponent_infinity_chart]
  rfl

/-- The full exterior smooth group component has the original reciprocal infinity coordinate. -/
@[reassoc] theorem positiveEqualityCycleSmoothMap_exterior_laurent :
    (ProjectiveLine.inversion K).hom ≫ M = L := by
  rw [positiveEqualityCycleSmoothMap_component]
  simp only [map_zero]
  change (ProjectiveLine.inversion K).hom ≫
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ (Z 0).left = _
  simpa only [ProjectiveLine.overlapRight, Category.assoc] using
    positiveEqualityCycleComponent_exterior_laurent hπ data D s hs hstart hk hp

/-- Every function of the original cubic is retained by the smooth exterior contraction. -/
@[reassoc] theorem positiveEqualityCycleSmoothMap_exterior_contraction :
    (ProjectiveLine.inversion K).hom ≫ M ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (finiteGlobalStructure hπ data (s + 1) hs) ≫
        finiteGlobalContraction hπ data (s + 1) hs =
      WeierstrassIntegralChart.infinityResidueContraction D (by omega) := by
  rw [positiveEqualityCycleSmoothMap_exterior_laurent_assoc, infinityLaurentChart_toCurve]

/-- The smooth exterior component is exactly the entire unchanged original infinity chart. -/
theorem positiveEqualityCycleSmoothMap_exterior_range :
    Set.range M = Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs) := by
  calc
    Set.range M = Set.range ((ProjectiveLine.inversion K).hom ≫ M) :=
      ((ProjectiveLine.inversion K).hom.homeomorph.surjective.range_comp M).symm
    _ = Set.range L := by
      rw [positiveEqualityCycleSmoothMap_exterior_laurent hπ data D s hs hstart hk hp]
      rfl
    _ = _ := infinityLaurentChart_range hπ data D (by omega) (s + 1) hs

end FLT.Mazur.WeierstrassDividedDepth
