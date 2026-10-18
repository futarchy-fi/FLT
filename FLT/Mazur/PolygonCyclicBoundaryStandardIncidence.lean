/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardBranch

/-!
# Exact standard-coordinate branch triangles in all tensor degrees

Both original branches use the exact standard node frame. These are the
specified zero and infinity maps, and the comparison holds for every positive
polygon size, including the one-gon, in every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction CyclicBoundaryParameter
open PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m) (n : ℕ) [NeZero n]
  (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
    CyclicBoundaryParameter.parameter (G K m) n)
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n)) (k : Fin m)
local notation "p" => PolygonAtlas.normalization K m
local notation "q" => PolygonAtlas.nodes K m
local notation "h" => PolygonAtlas.isPushout K m hm
local notation "e" => PolygonStandardFieldExtension.iso K L m hm

local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "v" => ProjectiveLineFieldExtension.componentIso K L
local notation "z" => ProjectiveLineFieldExtension.pointIso K L
local notation "F" => Over.pullback (g)
variable (l : Fin m) (s : point K ⟶ component K) (t : point L ⟶ component L)
  (w : s ≫ (componentι K m k ≫ PolygonAtlas.normalization K m) =
    nodeι K m l ≫ PolygonAtlas.nodes K m)
  (vst : t ≫ (ProjectiveLineFieldExtension.componentIso K L).hom =
    (ProjectiveLineFieldExtension.pointIso K L).hom ≫
      (Over.pullback (ProjectiveLineProductCharts.parameterToBase K L)).map s)

/-- Either specified standard branch retains the exact original node-frame triangle. -/
theorem standardNormalizationLine_node :
    LinePullbackTriangle t.left (standardComponent K L m hm n f j k).left
      (standardNode K L m hm n f j l).left
      (standardComponent_node K L m hm n f j k l s t w vst)
      (standardNormalizationLine K L m hm n f a i j k)
      (standardNormalizationEndpointLine K L m hm a i k l s t w vst)
      (standardNodeFrame K L m hm n f a i j l) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (standardNormalizationLine_section K L m hm n f a i j k)
    (standardNormalizationEndpointLine_section K L m hm a i k l s t w vst)
    (standardNodeFrame_section K L m hm n f a i j l)

/-- Every tensor degree retains the exact standard-coordinate branch triangle. -/
theorem standardNormalizationLine_node_power (d : ℕ) :
    LinePullbackTriangle t.left (standardComponent K L m hm n f j k).left
      (standardNode K L m hm n f j l).left
      (standardComponent_node K L m hm n f j k l s t w vst)
      (tensorPowerPullbackComparison _ (standardNormalizationLine K L m hm n f a i j k) d)
      (tensorPowerPullbackComparison _
        (standardNormalizationEndpointLine K L m hm a i k l s t w vst) d)
      (tensorPowerPullbackComparison _ (standardNodeFrame K L m hm n f a i j l) d) :=
  (standardNormalizationLine_node K L m hm n f a i j k l s t w vst).tensorPower d

/-- The actual zero branch on the chosen standard polygon retains the node frame in all degrees. -/
theorem standardNormalizationLine_zero_node (d : ℕ) :
    LinePullbackTriangle (ProjectiveLine.zeroSection L).left
      (standardComponent K L m hm n f j k).left (standardNode K L m hm n f j k).left
      (standardComponent_node K L m hm n f j k k
        (ProjectiveLine.zeroSection K) (ProjectiveLine.zeroSection L)
        (PolygonNodeIncidence.zero_node K m hm (p) (q) (h) k)
        (ProjectiveLineFieldExtension.zero_component K L))
      (tensorPowerPullbackComparison _ (standardNormalizationLine K L m hm n f a i j k) d)
      (tensorPowerPullbackComparison _
        (standardNormalizationEndpointLine K L m hm a i k k
          (ProjectiveLine.zeroSection K) (ProjectiveLine.zeroSection L)
          (PolygonNodeIncidence.zero_node K m hm (p) (q) (h) k)
          (ProjectiveLineFieldExtension.zero_component K L)) d)
      (tensorPowerPullbackComparison _ (standardNodeFrame K L m hm n f a i j k) d) :=
  standardNormalizationLine_node_power K L m hm n f a i j k k
    (ProjectiveLine.zeroSection K) (ProjectiveLine.zeroSection L)
    (PolygonNodeIncidence.zero_node K m hm (p) (q) (h) k)
    (ProjectiveLineFieldExtension.zero_component K L) d

/-- The actual adjacent infinity branch retains that same node frame in every tensor degree. -/
theorem standardNormalizationLine_infinity_node (d : ℕ) :
    LinePullbackTriangle (ProjectiveLine.infinitySection L).left
      (standardComponent K L m hm n f j (next hm k)).left
      (standardNode K L m hm n f j k).left
      (standardComponent_node K L m hm n f j (next hm k) k
        (ProjectiveLine.infinitySection K) (ProjectiveLine.infinitySection L)
        (PolygonNodeIncidence.infinity_node K m hm (p) (q) (h) k)
        (ProjectiveLineFieldExtension.infinity_component K L))
      (tensorPowerPullbackComparison _
        (standardNormalizationLine K L m hm n f a i j (next hm k)) d)
      (tensorPowerPullbackComparison _
        (standardNormalizationEndpointLine K L m hm a i (next hm k) k
          (ProjectiveLine.infinitySection K) (ProjectiveLine.infinitySection L)
          (PolygonNodeIncidence.infinity_node K m hm (p) (q) (h) k)
          (ProjectiveLineFieldExtension.infinity_component K L)) d)
      (tensorPowerPullbackComparison _ (standardNodeFrame K L m hm n f a i j k) d) :=
  standardNormalizationLine_node_power K L m hm n f a i j (next hm k) k
    (ProjectiveLine.infinitySection K) (ProjectiveLine.infinitySection L)
    (PolygonNodeIncidence.infinity_node K m hm (p) (q) (h) k)
    (ProjectiveLineFieldExtension.infinity_component K L) d

end FLT.Mazur.PolygonCyclicBoundary
