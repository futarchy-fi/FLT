/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RationalPadicMinimalTransport
public import FLT.FreyCurve.Serre.VeluLocalPointMorphism

/-!
# The original rational p-adic projective transport as an actual scheme point

The specified projective point homomorphism has the same generic scheme point
as the original field embedding and actual inverse variable change. This
identifies its values under a morphism on the specified generic equations.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry WeierstrassCurve WeierstrassCurve.Velu
open FLT.Mazur.WeierstrassIntegralChart
open scoped WeierstrassCurve.Affine

namespace FLT.Mazur

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (l : ℕ) [Fact l.Prime] [DecidableEq ℚ_[l]]
  (E : WeierstrassCurve ℚ) [E.IsElliptic]
  (W : WeierstrassCurve (padicIntegerSubring l)) (C : VariableChange ℚ_[l])
  (hC : C • E.map (algebraMap ℚ ℚ_[l]) =
    W.map (algebraMap (padicIntegerSubring l) ℚ_[l]))

local notation "WK" => W.map (algebraMap (padicIntegerSubring l) ℚ_[l])

/-- The original projective transport retains its actual generic affine scheme point. -/
theorem rationalPadicProjectiveHom_genericScheme (P : (E⁄ℚ).Point) :
    (projectiveToIntegral WK (rationalPadicProjectiveHom l E W C hC P)).left =
      affineSmoothPoint WK (ellipticExtensionPointHom (K := ℚ) E W C hC P) ≫
        (integralSmoothOpen WK).ι :=
  (projectiveToSmooth_inclusion WK _).symm

/-- Projecting the original local section gives the exact original rational scheme point. -/
@[reassoc] theorem rationalPadicProjectiveHom_genericProjection (P : (E⁄ℚ).Point) :
    (projectiveToIntegral WK (rationalPadicProjectiveHom l E W C hC P)).left ≫
        localGenericProjection E W C hC =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[l])) ≫
        (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) := by
  rw [rationalPadicProjectiveHom_genericScheme]
  exact ellipticExtensionPointHom_rational E W C hC P

variable (V : WeierstrassCurve ℚ) [V.IsElliptic]
  (U : WeierstrassCurve (padicIntegerSubring l)) (D : VariableChange ℚ_[l])
  (hD : D • V.map (algebraMap ℚ ℚ_[l]) =
    U.map (algebraMap (padicIntegerSubring l) ℚ_[l]))

local notation "UK" => U.map (algebraMap (padicIntegerSubring l) ℚ_[l])

/-- Actual generic morphisms preserve the specified original projective point transport. -/
@[reassoc] theorem rationalPadicProjectiveHom_genericMorphism
    (f : integralCurve E ⟶ integralCurve V) (g : integralCurve WK ⟶ integralCurve UK)
    (hg : g ≫ integralCurveStructure UK = integralCurveStructure WK)
    (hsq : g ≫ localGenericProjection V U D hD = localGenericProjection E W C hC ≫ f)
    (P : (E⁄ℚ).Point) (Q : (V⁄ℚ).Point)
    (hPQ : (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫ f =
      affineSmoothPoint V Q ≫ (integralSmoothOpen V).ι) :
    (projectiveToIntegral WK (rationalPadicProjectiveHom l E W C hC P)).left ≫ g =
      (projectiveToIntegral UK (rationalPadicProjectiveHom l V U D hD Q)).left := by
  rw [rationalPadicProjectiveHom_genericScheme, rationalPadicProjectiveHom_genericScheme]
  exact ellipticExtensionPointHom_morphism E V W U C D hC hD f g hg hsq P Q hPQ

end FLT.Mazur
