/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothContraction
public import FLT.Mazur.WeierstrassDividedInfinityLaurentZero
public import FLT.Mazur.ProjectiveLineMarkedCharts
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup

/-!
# The positive equality smooth identity is the original zero

The exterior cyclic coordinate is reciprocal to the retained infinity
coordinate. Both take value one at the original base-changed section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
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
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "G" => PolygonSplitGroup.model K (2 * s + 4)
local notation "M" => positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp

/-- The smooth group identity is the residue pullback of the original finite-model zero. -/
theorem positiveEqualityCycleSmoothMap_one :
    (η[G] ≫ M).left = finiteGlobalBaseChangeZero hπ data (s + 1) hs q ≫
      (pullbackSymmetry f q).hom := by
  have he := positiveEqualityCycleSmoothMap_exterior_laurent hπ data D s hs hstart hk hp
  have hi : η[MultiplicativeGroupScheme.gm K].left ≫ (ProjectiveLine.inversion K).hom =
      η[MultiplicativeGroupScheme.gm K].left := by
    rw [ProjectiveLineActionSpecialization.identity_left,
      ProjectiveLineMarkedCharts.unitPoint_inversion, inv_one]
  change η[MultiplicativeGroupScheme.gm K].left ≫
    (PolygonSplitGroup.component K (2 * s + 4) 0 ≫ M).left = _
  rw [← hi, Category.assoc, he]
  exact infinityLaurentChart_one hπ data D (by omega) (s + 1) hs

/-- The split smooth identity contracts to the same original projective zero section. -/
@[reassoc] theorem positiveEqualityCycleSmoothMap_one_contraction :
    (η[G] ≫ M).left ≫ pullback.snd q f ≫
        finiteGlobalContraction hπ data (s + 1) hs =
      q ≫ WeierstrassIntegralChart.integralCurveZero W := by
  rw [positiveEqualityCycleSmoothMap_one]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    finiteGlobalBaseChangeZero, pullback.lift_fst_assoc, finiteGlobalZero_contraction]

end FLT.Mazur.WeierstrassDividedDepth
