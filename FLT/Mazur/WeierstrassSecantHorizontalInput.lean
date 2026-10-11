/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantSmoothPresentation
public import FLT.Mazur.WeierstrassLeftSmoothHorizontalActionPresentation

/-!
# The original horizontal input on the concrete ordinary refinement

Restricting the original fraction-chart map to the secant principal open
preserves flatness and its coordinate contraction. Together with the genuine
smooth output comparison this supplies the integral presentation used by the
exceptional branch residue calculation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s : R) (a c : Coordinate W 2 →ₐ[R] S)
  (ψ : BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0) →+* S)
  (hc : c.toRingHom = ψ.comp (algebraMap (Coordinate W 2)
    (BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0))))
local notation "T" => SecantPairRing W a c
local notation "j" => IsScalarTower.toAlgHom R S T

/-- The original horizontal fraction input, restricted to the actual secant refinement. -/
def secantHorizontalInput :
    BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0) →+* T :=
  (algebraMap S T).comp ψ

include hc in
/-- The ordinary right input is precisely the restricted original horizontal fraction map. -/
theorem secantHorizontalInput_contraction :
    ((secantPairPresentation W a c).comp (ordinaryInputRight W false)).toRingHom =
      (secantHorizontalInput W s a c ψ).comp (algebraMap (Coordinate W 2)
        (BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0))) := by
  rw [secantPairPresentation_right]
  change (algebraMap S T).comp c.toRingHom = _
  rw [hc]
  rfl

/-- Restriction to the secant principal open is flat. -/
theorem secantPair_restriction_flat : RingHom.Flat (algebraMap S T) :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _
    (Submonoid.powers (a (coord W 2 0) - c (coord W 2 0))))

/-- A flat original horizontal input stays flat on the concrete ordinary refinement. -/
theorem secantHorizontalInput_flat (hflat : RingHom.Flat ψ) :
    RingHom.Flat (secantHorizontalInput W s a c ψ) :=
  hflat.comp (secantPair_restriction_flat W a c)

include hc in
/-- The retained horizontal denominator is the actual ordinary input X coordinate. -/
theorem secantHorizontalInput_denominator :
    secantHorizontalInput W s a c ψ
      (BlowupFractionChart.denominator (modificationChartCenter W s 2) (coord W 2 0)) =
        secantPairPresentation W a c (ordinaryInputRight W false (coord W 2 0)) := by
  exact (leftSmoothHorizontalInput_denominator W s
    ((secantPairPresentation W a c).comp (ordinaryInputRight W false)).toRingHom
    (secantHorizontalInput W s a c ψ) (secantHorizontalInput_contraction W s a c ψ hc)).symm

end FLT.Mazur.WeierstrassIntegralChart
