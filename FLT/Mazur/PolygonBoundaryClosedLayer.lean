/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryLayerQuotient
public import FLT.Mazur.PolygonInfinitesimalSpecialDivisor
public import FLT.Mazur.PolygonSpecialFiberIdeal

/-!
# The actual boundary reduction kernel is the original closed polygon line

The affine annihilator calculation and the original closed-fiber divisor
comparison identify every reduction kernel with the pushed-forward boundary
power on the original polygon, independently of the stage index.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original positive boundary line on the original closed polygon. -/
def closedBoundaryLine : (PolygonCyclicAtlas.scheme K n h).Modules :=
  divisorLineBundle
    (PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h) (fun _ ↦ 1))
    (specialBoundary_cartier K n h).1

/-- The original closed boundary is a line sheaf. -/
theorem closedBoundaryLine_rankOne : LocallyFreeRankOne (closedBoundaryLine K n h) :=
  (specialBoundary_cartier K n h).1.divisorLineBundle_locallyFreeRankOne

variable (m d : ℕ)

/-- Every original closed tensor power is the pullback of the stage tensor power. -/
def boundarySpecialTensorIso :
    (pullback (specialFiberInclusion K m n h)).obj
      (tensorPower (boundaryLine K m n h) d) ≅ tensorPower (closedBoundaryLine K n h) d :=
  tensorPowerIso (specialFiberInclusion K m n h) (boundaryLine K m n h) d ≪≫
    tensorPowerCongr (boundaryLineSpecialFiberIso K m n h) d

/-- The first parameter quotient is the specified original closed boundary power. -/
def boundarySpecialQuotientIso :
    quotient (stageParameterIdeal K m n h) (tensorPower (boundaryLine K m n h) d) 1 ≅
      (pushforward (specialFiberInclusion K m n h)).obj
        (tensorPower (closedBoundaryLine K n h) d) :=
  specialFiberLineQuotientIso K m n h _ ((boundaryLine_rankOne K m n h).tensorPower d) ≪≫
    (pushforward (specialFiberInclusion K m n h)).mapIso (boundarySpecialTensorIso K n h m d)

/-- The global reduction kernel is the actual original closed boundary power pushed forward. -/
def boundaryClosedLayerIso : (boundaryReductionSequence K m n h d).X₁ ≅
    (pushforward (specialFiberInclusion K (m + 1) n h)).obj
      (tensorPower (closedBoundaryLine K n h) d) :=
  (boundaryLayerQuotientIso K m n h d).symm ≪≫ boundarySpecialQuotientIso K n h (m + 1) d

/-- The quotient comparison retains the original closed tensor-degree pullback map. -/
@[reassoc] theorem projection_boundarySpecialQuotientIso :
    projection (stageParameterIdeal K m n h) (tensorPower (boundaryLine K m n h) d) 1 ≫
      (boundarySpecialQuotientIso K n h m d).hom =
    SectionGradedLinePullback.powerMap (specialFiberInclusion K m n h)
      (boundaryLineSpecialFiberIso K m n h) d := by
  rw [boundarySpecialQuotientIso, Iso.trans_hom, ← Category.assoc,
    projection_specialFiberLineQuotientIso]
  simp only [boundarySpecialTensorIso, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp,
    SectionGradedLinePullback.powerMap, SectionGradedPullback.powerMap,
    Adjunction.homEquiv_apply, Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages
