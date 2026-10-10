/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginDivisorCoordinates
public import FLT.Mazur.WeierstrassOriginIdealInvariant
public import FLT.Mazur.DivisorLinePullback

/-!
# Pullback of the original positive origin powers

The intrinsic positive line restricts to the genuine dual ideal on the
original parameter neighborhood. Every automorphism fixing the origin
preserves this line and its canonical section through the actual pullback.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The intrinsic positive line associated to the original origin power. -/
def originDivisorLine (n : ℕ) : (integralCurve W).Modules :=
  FCurve.divisorLineBundle ((integralCurveZero W).ker ^ n)
    (originIdealSheaf_power_effectiveCartier W n)

/-- Restrict the original positive line to the original parameter neighborhood. -/
def originDivisorNeighborhoodIso (n : ℕ) :
    (pullback (originNeighborhoodInclusion W)).obj (originDivisorLine W n) ≅
      FCurve.divisorLineBundle ((originNeighborhoodSection W).ker ^ n)
        (originNeighborhood_power_cartier W n) :=
  FCurve.divisorLinePullbackIsoOfEq _ (originIdealSheaf_power_effectiveCartier W n)
    (originNeighborhood_power_cartier W n) (originIdealSheaf_power_neighborhood W n)

/-- Restriction retains the original canonical divisor section. -/
theorem originDivisorNeighborhoodIso_canonical (n : ℕ) :
    (originDivisorNeighborhoodIso W n).hom.app ⊤
      (((pullback (originNeighborhoodInclusion W)).map
        (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n))).app ⊤
          ((FCurve.modulePullbackUnitIso (originNeighborhoodInclusion W)).inv.app ⊤
            (1 : Γ(Spec (.of (OriginNeighborhood W)), ⊤)))) =
      FCurve.divisorSection (originNeighborhood_power_cartier W n) ⊤ :=
  FCurve.divisorLinePullbackIsoOfEq_section_apply (originNeighborhoodInclusion W)
    (originIdealSheaf_power_effectiveCartier W n) (originNeighborhood_power_cartier W n)
    (originIdealSheaf_power_neighborhood W n) ⊤

/-- The actual pulled-back canonical section has the original parameter-power coordinate. -/
theorem originDivisorNeighborhoodIso_canonical_coordinate (n : ℕ) :
    originDivisorSectionsCoordinate W n ((originDivisorNeighborhoodIso W n).hom.app ⊤
      (((pullback (originNeighborhoodInclusion W)).map
        (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n))).app ⊤
          ((FCurve.modulePullbackUnitIso (originNeighborhoodInclusion W)).inv.app ⊤
            (1 : Γ(Spec (.of (OriginNeighborhood W)), ⊤))))) =
      originParameterSection W ^ n := by
  rw [originDivisorNeighborhoodIso_canonical, originDivisorSectionsCoordinate_canonical]

variable (e : integralCurve W ≅ integralCurve W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero W)

/-- An arbitrary original origin-preserving automorphism preserves each positive divisor line. -/
def originAutDivisorLineIso (n : ℕ) :
    (pullback e.hom).obj (originDivisorLine W n) ≅ originDivisorLine W n :=
  FCurve.divisorLinePullbackIsoOfEq _ (originIdealSheaf_power_effectiveCartier W n)
    (originIdealSheaf_power_effectiveCartier W n) (originAut_ideal_power_invariant W e hz n)

/-- The actual automorphism comparison preserves the canonical section morphism. -/
@[reassoc] theorem originAutDivisorLineIso_section (n : ℕ) :
    (pullback e.hom).map
        (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n)) ≫
        (originAutDivisorLineIso W e hz n).hom =
      (FCurve.modulePullbackUnitIso e.hom).hom ≫
        FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n) :=
  FCurve.divisorLinePullbackIsoOfEq_section e.hom
    (originIdealSheaf_power_effectiveCartier W n) (originIdealSheaf_power_effectiveCartier W n)
    (originAut_ideal_power_invariant W e hz n)

end FLT.Mazur.WeierstrassIntegralChart
