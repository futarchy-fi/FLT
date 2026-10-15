/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLayerQuotient
public import FLT.Mazur.PolygonArithmeticResidueLine
public import FLT.Mazur.PolygonArithmeticResidueIdeal
public import FLT.Mazur.PolygonBoundaryClosedLayer

/-!
# The actual boundary reduction kernel is the original closed polygon line

The affine annihilator calculation and the original closed-fiber divisor
comparison identify every reduction kernel with the pushed-forward boundary
power on the original polygon, independently of the stage index.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsDomain A] (π : A) (hne : π ≠ 0)
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (hπ : algebraMap A (IsLocalRing.ResidueField A) π = 0)
  (n : ℕ) (h : 2 ≤ n) [NeZero n] (m d : ℕ)
local notation "K" => IsLocalRing.ResidueField A
open PolygonInfinitesimalStages (closedBoundaryLine)

/-- Every original closed tensor power is the pullback of the stage tensor power. -/
def boundaryResidueTensorIso :
    (pullback (residueFiberInclusion A π hπ m n h)).obj
      (tensorPower (boundaryLine A π m n h) d) ≅ tensorPower (closedBoundaryLine K n h) d :=
  tensorPowerIso (residueFiberInclusion A π hπ m n h) (boundaryLine A π m n h) d ≪≫
    tensorPowerCongr (boundaryLineResidueIso A π hπ m n h) d

/-- The first parameter quotient is the specified original closed boundary power. -/
def boundaryResidueQuotientIso :
    quotient (stageParameterIdeal A π m n h) (tensorPower (boundaryLine A π m n h) d) 1 ≅
      (pushforward (residueFiberInclusion A π hπ m n h)).obj
        (tensorPower (closedBoundaryLine K n h) d) :=
  residueFiberLineQuotientIso A π hgen hπ m n h _
      ((boundaryLine_rankOne A π m n h).tensorPower d) ≪≫
    (pushforward (residueFiberInclusion A π hπ m n h)).mapIso
      (boundaryResidueTensorIso A π hπ n h m d)

/-- The global reduction kernel is the actual original closed boundary power pushed forward. -/
def boundaryClosedLayerIso : (boundaryReductionSequence A π m n h d).X₁ ≅
    (pushforward (residueFiberInclusion A π hπ (m + 1) n h)).obj
      (tensorPower (closedBoundaryLine K n h) d) :=
  (boundaryLayerQuotientIso A π m n h hne d).symm ≪≫
    boundaryResidueQuotientIso A π hgen hπ n h (m + 1) d

omit [IsNoetherianRing A] [IsDomain A] in
/-- The quotient comparison retains the original closed tensor-degree pullback map. -/
@[reassoc] theorem projection_boundaryResidueQuotientIso :
    projection (stageParameterIdeal A π m n h) (tensorPower (boundaryLine A π m n h) d) 1 ≫
      (boundaryResidueQuotientIso A π hgen hπ n h m d).hom =
    SectionGradedLinePullback.powerMap (residueFiberInclusion A π hπ m n h)
      (boundaryLineResidueIso A π hπ m n h) d := by
  rw [boundaryResidueQuotientIso, Iso.trans_hom, ← Category.assoc,
    projection_residueFiberLineQuotientIso]
  simp only [boundaryResidueTensorIso, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp,
    SectionGradedLinePullback.powerMap, SectionGradedPullback.powerMap,
    Adjunction.homEquiv_apply, Category.assoc]

end FLT.Mazur.PolygonArithmeticStages
