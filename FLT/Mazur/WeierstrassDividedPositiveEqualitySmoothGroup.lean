/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityAction
public import FLT.Mazur.PolygonActionSmooth
import all FLT.Mazur.WeierstrassDividedPositiveEqualityPushout

/-!
# The complete smooth group of the positive-start equality fiber

The full smooth locus is the disjoint union of the original Laurent
components. Its split-group coordinates retain the whole-fiber action.
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
local notation "V" => Over.mk p
local notation "G" => PolygonSplitGroup.model K (2 * s + 4)
local notation "H" => positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp

include D hstart hk hp in
/-- The actual residue model is locally of finite presentation by its proved pinching cocone. -/
theorem positiveEqualityCycleStructure_lfp : LocallyOfFinitePresentation p :=
  PolygonPinching.polygon_lfp K (2 * s + 4) (by omega) N Q H

include D hstart hk hp in
/-- The whole smooth locus consists exactly of the original punctured cyclic components. -/
theorem positiveEqualityCycle_smooth_range :
    let _ : LocallyOfFinitePresentation (V).hom :=
      positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
    ((V).hom.smoothLocus : Set (V).left) =
      ⋃ i : Fin (2 * s + 4), Set.range (PolygonPinching.torusToComponent K ≫ Z i).left := by
  let _ : LocallyOfFinitePresentation (V).hom :=
    positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
  simpa only [positiveEqualityCycleNormalization_ι] using
    PolygonPinching.smooth_range K (2 * s + 4) (by omega) N Q H

/-- The complete original smooth locus has the split group's specified component coordinates. -/
def positiveEqualityCycleSmoothIso :
    let _ : LocallyOfFinitePresentation (V).hom :=
      positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
    PolygonPinching.smoothPolygon K (C := V) ≅ G := by
  let _ : LocallyOfFinitePresentation (V).hom :=
    positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
  exact PolygonPinching.smoothIso K (2 * s + 4) (by omega) N Q H

/-- The split group maps into the whole original fiber through its complete smooth locus. -/
def positiveEqualityCycleSmoothMap : G ⟶ V := by
  let _ : LocallyOfFinitePresentation (V).hom :=
    positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
  exact (positiveEqualityCycleSmoothIso hπ data D s hs hstart hk hp).inv ≫
    PolygonActionSmooth.smoothι K

/-- Each smooth group component is exactly its original punctured normalization component. -/
@[reassoc] theorem positiveEqualityCycleSmoothMap_component (a : ZMod (2 * s + 4)) :
    PolygonSplitGroup.component K (2 * s + 4) a ≫
        positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp =
      PolygonPinching.torusToComponent K ≫ Z ((ZMod.finEquiv (2 * s + 4)).symm a) := by
  let _ : LocallyOfFinitePresentation (V).hom :=
    positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
  simpa only [positiveEqualityCycleSmoothMap, positiveEqualityCycleSmoothIso,
    PolygonActionSmooth.smoothMap, positiveEqualityCycleNormalization_ι] using
    PolygonActionSmooth.component_smoothMap K (2 * s + 4) (by omega) N Q H a

/-- The whole-fiber action restricts to multiplication on the complete smooth split group. -/
theorem positiveEqualityCycleAction_smooth_restriction :
    G ◁ positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp ≫
        positiveEqualityCycleAction hπ data D s hs hstart hk hp =
      μ[G] ≫ positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp := by
  let _ : LocallyOfFinitePresentation (V).hom :=
    positiveEqualityCycleStructure_lfp hπ data D s hs hstart hk hp
  unfold positiveEqualityCycleSmoothMap positiveEqualityCycleSmoothIso
    positiveEqualityCycleAction
  exact PolygonActionSmooth.model_restriction K (2 * s + 4) (by omega) N Q H

end FLT.Mazur.WeierstrassDividedDepth
