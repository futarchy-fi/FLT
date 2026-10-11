/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityIdentityComponent
public import FLT.Mazur.WeierstrassInfinityResidueSmoothGroup
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup

/-!
# The original smooth cubic embeds as the complete identity component

This map retains the actual contraction to the original integral cubic.
Its image is the entire connected smooth component of the original zero,
and its Laurent orientation is reciprocal to the cyclic coordinate.
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
open WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "e" => infinityResidueSmoothIso D hd
local notation "M" => Over.Hom.left (PolygonSplitGroup.component K (2 * s + 4) 0 ≫
  positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp)

include hk in
/-- The original full smooth residue cubic embeds in the actual modified fiber. -/
def positiveEqualityOriginalSmoothMap :
    (integralSmoothOpen V).toScheme ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs :=
  (e).inv ≫ infinityLaurentChart hπ data D hd (s + 1) hs

instance positiveEqualityOriginalSmoothMap_isOpenImmersion :
    IsOpenImmersion (positiveEqualityOriginalSmoothMap hπ data D s hs hk) := by
  unfold positiveEqualityOriginalSmoothMap
  infer_instance

/-- The original smooth embedding retains its actual cubic contraction on every function. -/
@[reassoc] theorem positiveEqualityOriginalSmoothMap_contraction :
    positiveEqualityOriginalSmoothMap hπ data D s hs hk ≫
        pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs =
      (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W := by
  apply (cancel_epi (e).hom).mp
  simp only [positiveEqualityOriginalSmoothMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [infinityLaurentChart_toCurve, infinityResidueSmoothIso_contraction]

/-- The original smooth embedding covers the complete retained infinity tensor chart. -/
theorem positiveEqualityOriginalSmoothMap_range :
    Set.range (positiveEqualityOriginalSmoothMap hπ data D s hs hk) =
      Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs) := by
  calc
    _ = Set.range (infinityLaurentChart hπ data D hd (s + 1) hs) :=
      (e).inv.homeomorph.surjective.range_comp _
    _ = _ := infinityLaurentChart_range hπ data D hd (s + 1) hs

/-- The entire original smooth cubic is exactly the connected component of the original zero. -/
theorem positiveEqualityOriginalSmoothMap_component (x : Spec (.of K)) :
    let _ := positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
    (pullback.fst q f).smoothLocus.ι ''
        connectedComponent (positiveEqualitySmoothZero hπ data D s hs hstart hk hp x) =
      Set.range (positiveEqualityOriginalSmoothMap hπ data D s hs hk) := by
  let _ := positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
  dsimp only
  rw [positiveEqualitySmoothZero_component_image, positiveEqualityOriginalSmoothMap_range]

/-- Cyclic orientation is exactly the reciprocal of the original smooth cubic parameter. -/
@[reassoc] theorem positiveEqualityCycleSmoothMap_originalSmooth :
    (ProjectiveLine.inversion K).hom ≫ M =
      (e).hom ≫ positiveEqualityOriginalSmoothMap hπ data D s hs hk := by
  rw [positiveEqualityOriginalSmoothMap, Iso.hom_inv_id_assoc]
  exact positiveEqualityCycleSmoothMap_exterior_laurent hπ data D s hs hstart hk hp

end FLT.Mazur.WeierstrassDividedDepth
