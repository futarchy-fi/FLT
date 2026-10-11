/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothFractionActionCover
public import FLT.Mazur.RegularCenterQuotientOpenRatios

/-!
# Original ratios of the genuine smooth fraction action

These formulas specialize the regular-center quotient identities to the
actual action cover. They retain the scale/X and Y/X coordinates on its
horizontal member, including arbitrary residue restrictions.
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

open RegularCenter WeierstrassModificationReesCoordinates BlowupFractionChart
local notation "I" => modificationChartCenter W s 2
local notation "z" => ψ (denominator I f)
local notation "H" => leftSmoothFractionAction_principal W s b3 b4 b6
  h3 h4 h6 p α β hp hα f hf ψ hβ
local notation "Q" => quotient I α z H
local notation "O" => LeftSmoothFractionActionOpen W s b3 b4 b6
  h3 h4 h6 p α β hp hα f hf ψ hβ
local notation "L" => leftSmoothFractionActionLift W s b3 b4 b6
  h3 h4 h6 p α β hp hα f hf ψ hβ hflat

/-- On the actual action cover, every original fraction is a ratio of center quotients. -/
theorem leftSmoothFractionActionLift_ratio (i : Fin 3)
    (a : Coordinate W 2) (ha : a ∈ I) :
    algebraMap S (O i) (Q (centerGenerators W s i) (centerGenerators_mem W s i)) *
        L i (ratio I (centerGenerators W s i) a ha) = algebraMap S (O i) (Q a ha) := by
  rw [leftSmoothFractionActionLift_def]
  exact quotient_mul_quotientOpenLift_ratio ..

variable {C : Type u} [CommRing C]

/-- The actual original scale/X coordinate remains controlled after residue restriction. -/
theorem leftSmoothFractionActionLift_horizontalScale (e :
    LeftSmoothFractionActionOpen W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ 1 →+* C) :
    e (algebraMap S (O 1) (Q (coord W 2 0) (centerGenerators_mem W s 1))) *
        e (L 1 (horizontalScale W s)) =
      e (algebraMap S (O 1)
        (Q (algebraMap R (Coordinate W 2) s) (centerGenerators_mem W s 0))) := by
  rw [← map_mul]
  exact congrArg e (leftSmoothFractionActionLift_ratio W s b3 b4 b6 h3 h4 h6
    p α β hp hα f hf ψ hβ hflat 1 _ (centerGenerators_mem W s 0))

/-- The actual original Y/X coordinate uses the same horizontal quotient multiplier. -/
theorem leftSmoothFractionActionLift_horizontalVertical (e :
    LeftSmoothFractionActionOpen W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ 1 →+* C) :
    e (algebraMap S (O 1) (Q (coord W 2 0) (centerGenerators_mem W s 1))) *
        e (L 1 (horizontalVertical W s)) =
      e (algebraMap S (O 1) (Q (coord W 2 1) (centerGenerators_mem W s 2))) := by
  rw [← map_mul]
  exact congrArg e (leftSmoothFractionActionLift_ratio W s b3 b4 b6 h3 h4 h6
    p α β hp hα f hf ψ hβ hflat 1 _ (centerGenerators_mem W s 2))

/-- The horizontal quotient multiplier is a unit on every residue of this actual cover member. -/
theorem leftSmoothFractionActionLift_horizontal_isUnit (e :
    LeftSmoothFractionActionOpen W s b3 b4 b6 h3 h4 h6 p α β hp hα f hf ψ hβ 1 →+* C) :
    IsUnit (e (algebraMap S (O 1) (Q (coord W 2 0) (centerGenerators_mem W s 1)))) :=
  quotientOpen_generator_specialize_isUnit I α z H _ (centerGenerators_mem W s 1) e

end FLT.Mazur.WeierstrassIntegralChart
