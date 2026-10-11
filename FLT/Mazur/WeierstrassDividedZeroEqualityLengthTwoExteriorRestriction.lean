/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoGlobalDesc
public import FLT.Mazur.WeierstrassModificationXIncidenceBranchCover
public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoBranches
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoAtlas
import all FLT.Mazur.WeierstrassDividedZeroEqualityExteriorMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoLocalMaps

/-!
# Global cyclic descent on the entire original exterior component

The two localized incidence branches determine the whole affine incidence
line. Together with the unchanged infinity chart they determine the exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityLengthTwoGlobalDesc hπ data D hs hstart hk hp F w

local notation "Z" => zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp

local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 (data (Fin.mk 1 (by omega))))
local notation "ha" => D.a₁_unit.map (residue R)
local notation "u" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "E" => zeroRetainedExteriorOrientedIso hπ data D 0 (by omega) 0
  (by omega) (by omega) (by omega)
local notation "l" => zeroRetainedExteriorAffineChart hπ data D 0 (by omega) 0
  (by omega) (by omega) (by omega)
local notation "ι" => zeroRetainedExteriorInfinityChart hπ data D 0 (by omega) 0
  (by omega) (by omega) (by omega)

/-- Descent recovers the entire affine exterior incidence line in its original coordinate. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_exterior_affine :
    ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ (Z 0).left ≫ d =
      ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ F 0 := by
  apply fullNodeIncidenceBranches_hom_ext a c ha
  · rw [zeroEqualityCycleComponent_lengthTwo_first_exterior_assoc
      hπ data D hs hstart hk hp,
      zeroEqualityLengthTwoGlobalDesc_first,
      zeroEqualityLengthTwoFirstDesc_exterior]
  · rw [zeroEqualityCycleComponent_lengthTwo_second_exterior_assoc
      hπ data D hs hstart hk hp,
      zeroEqualityLengthTwoGlobalDesc_second,
      zeroEqualityLengthTwoSecondDesc_exterior]

/-- Descent recovers the full original infinity chart of the exterior. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_exterior_infinity :
    ι ≫ (E).hom ≫ (Z 0).left ≫ d = ι ≫ (E).hom ≫ F 0 := by
  rw [zeroEqualityCycleComponent_infinity_chart_assoc]
  change globalTensorAtlasMap hπ data K (0 + 1) hs 0 ≫ d = _
  rw [zeroEqualityLengthTwoGlobalDesc_atlas]
  rfl

/-- The complete exterior projective component recovers its prescribed family member. -/
@[reassoc] theorem zeroEqualityLengthTwoGlobalDesc_exterior_component :
    (Z 0).left ≫ d = F 0 := by
  apply (cancel_epi (E).hom).mp
  apply pushout.hom_ext
  · change l ≫ (E).hom ≫ (Z 0).left ≫ d = l ≫ (E).hom ≫ F 0
    rw [zeroRetainedExteriorOrientedIso_affine_assoc,
      zeroRetainedExteriorOrientedIso_affine_assoc]
    exact zeroEqualityLengthTwoGlobalDesc_exterior_affine hπ data D hs hstart hk hp F w
  · exact zeroEqualityLengthTwoGlobalDesc_exterior_infinity hπ data D hs hstart hk hp F w

end FLT.Mazur.WeierstrassDividedDepth
