/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitZero
public import FLT.Mazur.PolygonSplitGroupConnected
import all FLT.Mazur.WeierstrassDividedPositiveSplitSmoothGroup

/-!
# The full connected smooth identity component of the actual strict fiber

The connected component at the retained original zero has exactly the
entire original infinity tensor chart as its image in the modified fiber.
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
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "p" => pullback.fst q f
local notation "G" => PolygonSplitGroup.model K (2 * s + 5)
local notation "e" => positiveSplitCycleSmoothIso hπ data D s hs hstart hk hp

/-- The original finite-model zero factors through the whole actual smooth locus. -/
def positiveSplitSmoothZero :
    let _ := positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
    Spec (.of K) ⟶ (p).smoothLocus.toScheme := by
  let _ := positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
  exact η[G].left ≫ (e).inv.left

/-- The chosen smooth factor is still the exact residue pullback of the original zero. -/
@[reassoc] theorem positiveSplitSmoothZero_inclusion :
    let _ := positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
    positiveSplitSmoothZero hπ data D s hs hstart hk hp ≫ (p).smoothLocus.ι =
      finiteGlobalBaseChangeZero hπ data (s + 1) hs q ≫ (pullbackSymmetry f q).hom := by
  let _ := positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
  exact positiveSplitCycleSmoothMap_one hπ data D s hs hstart hk hp

/-- Its entire connected smooth identity component is the full original infinity chart. -/
theorem positiveSplitSmoothZero_component_image (x : Spec (.of K)) :
    let _ := positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
    (p).smoothLocus.ι ''
        connectedComponent (positiveSplitSmoothZero hπ data D s hs hstart hk hp x) =
      Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs) := by
  let _ := positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
  have he := PolygonSplitGroup.connectedComponent_iso_one K (2 * s + 5)
    ((Over.forget _).mapIso (e).symm) x
  change connectedComponent (positiveSplitSmoothZero hπ data D s hs hstart hk hp x) =
    Set.range ((PolygonSplitGroup.component K (2 * s + 5) 0).left ≫ (e).inv.left) at he
  dsimp only
  rw [he, ← Set.range_comp]
  change Set.range (PolygonSplitGroup.component K (2 * s + 5) 0 ≫
    positiveSplitCycleSmoothMap hπ data D s hs hstart hk hp).left = _
  exact positiveSplitCycleSmoothMap_exterior_range hπ data D s hs hstart hk hp

end FLT.Mazur.WeierstrassDividedDepth
