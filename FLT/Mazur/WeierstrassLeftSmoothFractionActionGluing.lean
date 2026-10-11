/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothFractionActionCover
public import FLT.Mazur.RegularCenterGluedLift

/-!
# The glued lift of an affine presentation of the actual smooth action

The complete quotient-open cover and its actual overlap maps glue to a map
into the original affine-center Rees modification. The contraction is the
original smooth action presentation. Assembly across the projective input
and output atlas and finite modification iteration are separate steps.
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

/-- The actual smooth action on this entire affine presentation lifts to the original Rees Proj. -/
irreducible_def leftSmoothFractionActionToRees :
    Spec (.of S) ⟶ BlowupRees.proj (modificationChartCenter W s 2) :=
  RegularCenter.gluedLift (modificationChartCenter W s 2) α
    (ψ (BlowupFractionChart.denominator (modificationChartCenter W s 2) f))
    (leftSmoothFractionAction_principal W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ)
    (flatRingHom_isRegular
      (A := BlowupFractionChart.chart (modificationChartCenter W s 2) f) (B := S) ψ hflat
      (BlowupFractionChart.denominator_regular (modificationChartCenter W s 2) f))
    (WeierstrassModificationReesCoordinates.centerGenerators W s)
    (WeierstrassModificationReesCoordinates.centerGenerators_mem W s)
    (WeierstrassModificationReesCoordinates.centerGenerators_span W s)

/-- The lift contracts to exactly the given original smooth action in affine coordinates. -/
@[reassoc] theorem leftSmoothFractionActionToRees_contraction :
    leftSmoothFractionActionToRees W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ hflat ≫
        BlowupRees.contraction (modificationChartCenter W s 2) =
      Spec.map (CommRingCat.ofHom α) := by
  rw [leftSmoothFractionActionToRees_def, RegularCenter.gluedLift_contraction]

/-- Every quotient-open restriction of the glued lift is the constructed original fraction lift. -/
@[reassoc] theorem leftSmoothFractionActionCover_toRees (i : Fin 3) :
    (leftSmoothFractionActionCover W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ hflat).f i ≫
        leftSmoothFractionActionToRees W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ hflat =
      Spec.map (CommRingCat.ofHom
        (leftSmoothFractionActionLift W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ hflat i)) ≫
          BlowupRees.fractionChartInclusion (modificationChartCenter W s 2)
            (WeierstrassModificationReesCoordinates.centerGenerators W s i)
            (WeierstrassModificationReesCoordinates.centerGenerators_mem W s i) := by
  rw [leftSmoothFractionActionToRees_def]
  unfold leftSmoothFractionActionCover
  rw [RegularCenter.quotientCover_gluedLift, RegularCenter.quotientOpenToProj,
    leftSmoothFractionActionLift_def]

end FLT.Mazur.WeierstrassIntegralChart
