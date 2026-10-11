/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAffineCenterEquality
public import FLT.Mazur.WeierstrassModificationReesProjCover
public import FLT.Mazur.RegularCenterRatioCover

/-!
# Complete ratio covers on affine presentations of the modified smooth input

For a flat presentation over any original fraction chart, and an affine output
presentation of the genuine smooth action, the three output-center quotients
give a cover of the whole input presentation. Each member maps into its actual
original output fraction chart. No original denominator or scale is inverted.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s * b6)
  {S : Type u} [CommRing S]
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme) (α β : Coordinate W 2 →+* S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) ≫ integralCurveStructure W)
  (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W 2 =
    leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) hp)
  (f : Coordinate W 2) (hf : f ∈ modificationChartCenter W s 2)

variable (ψ : BlowupFractionChart.chart (modificationChartCenter W s 2) f →+* S)
  (hβ : β = ψ.comp
    (algebraMap (Coordinate W 2) (BlowupFractionChart.chart (modificationChartCenter W s 2) f)))
  (hflat : RingHom.Flat
    (R := BlowupFractionChart.chart (modificationChartCenter W s 2) f) (S := S) ψ)

include h3 h4 h6 hp hα hf hβ in
/-- The actual affine action output is principalized by the retained input denominator. -/
theorem leftSmoothFractionAction_principal :
    (modificationChartCenter W s 2).map α = Ideal.span {ψ (BlowupFractionChart.denominator
      (modificationChartCenter W s 2) f)} := by
  rw [leftSmoothAffinePresentation_center_eq W s b3 b4 b6 h3 h4 h6 p α β hp hα, hβ]
  exact BlowupFractionChart.center_map_eq_mapped_denominator (modificationChartCenter W s 2) f hf ψ

/-- The actual output-center ratios cover the complete modified input presentation. -/
def leftSmoothFractionActionCover : (Spec (.of S)).AffineOpenCover :=
  RegularCenter.quotientCover (modificationChartCenter W s 2) α
    (ψ (BlowupFractionChart.denominator (modificationChartCenter W s 2) f))
    (leftSmoothFractionAction_principal W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ)
    (flatRingHom_isRegular
      (A := BlowupFractionChart.chart (modificationChartCenter W s 2) f) (B := S) ψ hflat
      (BlowupFractionChart.denominator_regular (modificationChartCenter W s 2) f))
    (WeierstrassModificationReesCoordinates.centerGenerators W s)
    (WeierstrassModificationReesCoordinates.centerGenerators_mem W s)
    (WeierstrassModificationReesCoordinates.centerGenerators_span W s)

/-- The actual coordinate ring of one quotient open in the modified input. -/
abbrev LeftSmoothFractionActionOpen (i : Fin 3) :=
  RegularCenter.QuotientOpen (modificationChartCenter W s 2) α
    (ψ (BlowupFractionChart.denominator (modificationChartCenter W s 2) f))
    (leftSmoothFractionAction_principal W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ)
    (WeierstrassModificationReesCoordinates.centerGenerators W s i)
    (WeierstrassModificationReesCoordinates.centerGenerators_mem W s i)

/-- A lift of the genuine action into each original output fraction chart on its ratio open. -/
irreducible_def leftSmoothFractionActionLift (i : Fin 3) :
    BlowupFractionChart.chart (modificationChartCenter W s 2)
      ((WeierstrassModificationReesCoordinates.centerGenerators W s) i) →+*
      LeftSmoothFractionActionOpen W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ i :=
  RegularCenter.quotientOpenLift (modificationChartCenter W s 2) α
    (ψ (BlowupFractionChart.denominator (modificationChartCenter W s 2) f))
    (leftSmoothFractionAction_principal W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ)
    (WeierstrassModificationReesCoordinates.centerGenerators W s i)
    (WeierstrassModificationReesCoordinates.centerGenerators_mem W s i)
    (flatRingHom_isRegular
      (A := BlowupFractionChart.chart (modificationChartCenter W s 2) f) (B := S) ψ hflat
      (BlowupFractionChart.denominator_regular (modificationChartCenter W s 2) f))

/-- Every original action coordinate is retained by the local lift. -/
@[simp] theorem leftSmoothFractionActionLift_base (i : Fin 3) (z : Coordinate W 2) :
    leftSmoothFractionActionLift W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ hflat i
        (algebraMap _ _ z) =
      algebraMap S
        (LeftSmoothFractionActionOpen W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ i) (α z) := by
  rw [leftSmoothFractionActionLift_def, RegularCenter.quotientOpenLift_base]
  rfl

/-- Each cover member is the spectrum of the actual quotient localization. -/
theorem leftSmoothFractionActionCover_map (i : Fin 3) :
    (leftSmoothFractionActionCover W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ hflat).f i =
      Spec.map (CommRingCat.ofHom (algebraMap S
        (LeftSmoothFractionActionOpen W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ i))) := rfl

end FLT.Mazur.WeierstrassIntegralChart
