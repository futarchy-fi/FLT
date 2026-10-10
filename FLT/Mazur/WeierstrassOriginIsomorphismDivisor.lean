/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginDivisorPullback

/-!
# Intrinsic origin-divisor pullback between distinct cubics

An actual origin-preserving isomorphism identifies the full ideal of the
target origin with the source ideal, its powers, and their positive lines.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (e : integralCurve W ≅ integralCurve V)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

include hz in
/-- The full target origin ideal pulls back to the full source origin ideal. -/
theorem originIso_ideal_comap :
    (integralCurveZero V).ker.comap e.hom = (integralCurveZero W).ker := by
  have h := ProjectiveLineMarkedCharts.ker_comap_mono (integralCurveZero W) e.hom
  rwa [hz] at h

include hz in
/-- Every scheme-theoretic origin power is retained by the actual pullback. -/
theorem originIso_ideal_power_comap (n : ℕ) :
    ((integralCurveZero V).ker ^ n).comap e.hom = (integralCurveZero W).ker ^ n := by
  rw [FCurve.idealSheaf_comap_pow, originIso_ideal_comap W V e hz]

/-- The intrinsic positive origin line on the target pulls back to the source line. -/
def originIsoDivisorLineIso (n : ℕ) :
    (pullback e.hom).obj (originDivisorLine V n) ≅ originDivisorLine W n :=
  FCurve.divisorLinePullbackIsoOfEq _ (originIdealSheaf_power_effectiveCartier V n)
    (originIdealSheaf_power_effectiveCartier W n) (originIso_ideal_power_comap W V e hz n)

/-- The line comparison retains the original canonical section morphism. -/
@[reassoc] theorem originIsoDivisorLineIso_section (n : ℕ) :
    (pullback e.hom).map
        (FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier V n)) ≫
        (originIsoDivisorLineIso W V e hz n).hom =
      (FCurve.modulePullbackUnitIso e.hom).hom ≫
        FCurve.divisorSectionMap (originIdealSheaf_power_effectiveCartier W n) :=
  FCurve.divisorLinePullbackIsoOfEq_section e.hom
    (originIdealSheaf_power_effectiveCartier V n) (originIdealSheaf_power_effectiveCartier W n)
    (originIso_ideal_power_comap W V e hz n)

end FLT.Mazur.WeierstrassIntegralChart
