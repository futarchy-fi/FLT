/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonPinchingCompleteClosedComparison
public import FLT.Mazur.WeierstrassDividedZeroEqualityPolygonIso

import all FLT.Mazur.WeierstrassDividedZeroEqualityPositivePushout
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoPushout

import all FLT.Mazur.PolygonPinchingCompleteClosedComparison

/-!
# The entire even cyclic arithmetic model in the complete closed fiber

Apply the proved original pinching cocone, retaining all complete components
and every singular node. The comparison uses the original cyclic coordinates;
no assertion about the independently reparametrized smooth atlas is made.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonInfinitesimalStages PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeClosedFiberInclusion
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K))) f
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart (by omega) hp
local notation "N" => zeroEqualityCycleNormalization hπ data D s hs hstart (by omega) hp
local notation "Q" => zeroEqualityCycleNodes hπ data D s hs (by omega)
local notation "hN" => zeroEqualityCycleCocone_isPushout hπ data D s hs hstart (by omega) hp
local notation "c" => exactVeroneseProjToBase K (2 * s + 2) (by omega)

/-- The full original arithmetic residue model, including its singular nodes. -/
def evenCompleteClosedIso : finiteGlobalTensorModel hπ data K (s + 1) hs ≅
    pullback c (completeClosedBase K) :=
  pinchingCompleteClosedIso K (2 * s + 2) (by omega) N Q hN

/-- The entire comparison retains the original residue field. -/
@[reassoc] theorem evenCompleteClosedIso_snd :
    (evenCompleteClosedIso hπ data D s hs hstart hp).hom ≫ pullback.snd _ _ = p :=
  pinchingCompleteClosedIso_snd K (2 * s + 2) (by omega) N Q hN

/-- Every full original projective component maps to the same complete closed component. -/
@[reassoc] theorem evenCompleteClosedIso_component (i : Fin (2 * s + 2)) :
    (Z i).left ≫ (evenCompleteClosedIso hπ data D s hs hstart hp).hom ≫ pullback.fst _ _ =
      (componentι K (2 * s + 2) i ≫
        PolygonCyclicAtlas.normalization K (2 * s + 2) (by omega)).left ≫
          completeClosedFiberInclusion K (2 * s + 2) (by omega) := by
  rw [← zeroEqualityCycleNormalization_ι hπ data D s hs hstart (by omega) hp i]
  exact pinchingCompleteClosedIso_component K (2 * s + 2) (by omega) N Q hN i

/-- Every original singular section maps to the same singular section in the complete family. -/
@[reassoc] theorem evenCompleteClosedIso_node (i : Fin (2 * s + 2)) :
    (equalityNodeOverSection hπ data D s hs (by omega)
      (zeroEqualityCycleNodeIndex start s i)).left ≫
        (evenCompleteClosedIso hπ data D s hs hstart hp).hom ≫ pullback.fst _ _ =
      (nodeι K (2 * s + 2) i ≫
        PolygonCyclicAtlas.nodes K (2 * s + 2) (by omega)).left ≫
          completeClosedFiberInclusion K (2 * s + 2) (by omega) := by
  rw [← zeroEqualityCycleNodes_ι hπ data D s hs (by omega) i]
  exact pinchingCompleteClosedIso_node K (2 * s + 2) (by omega) N Q hN i

end FLT.Mazur.WeierstrassDividedDepth
