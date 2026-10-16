/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialTerminalEvaluationRestriction
public import FLT.Mazur.WeierstrassModificationXInitialTerminalPunctureIso
public import FLT.Mazur.NodalFiberPunctureCoefficientMap

/-!
# Initial terminal puncture identifications commute with quotient restriction

The complete terminal D(q) and D(p) comparisons retain the original initial
Laurent parameter and label under the actual consecutive coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (opposite : Bool)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "c₀" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "c₁" => WeierstrassDilatation.arithmeticTerminalSmoothing π (m + 1) W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "hc" => WeierstrassDilatation.arithmeticTerminalSmoothing_restriction
  R π m W s b3 b4 b6 ha hs h2 h4 h6
local notation "N" => NodalFiber.coefficientRingMap f c₁ c₀ hc
local notation "E₀" => initialTerminalArithmeticNodeEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "E₁" => initialTerminalArithmeticNodeEvaluation
  π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "δ₀" => ite (opposite = true) (NodalFiber.p c₀) (NodalFiber.q c₀)
local notation "δ₁" => ite (opposite = true) (NodalFiber.p c₁) (NodalFiber.q c₁)
local notation "L₀" => Localization.Away δ₀
local notation "L₁" => Localization.Away δ₁
local notation "i₀" => Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate c₀) L₀))
local notation "i₁" => Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate c₁) L₁))
local notation "P" => Spec.map (CommRingCat.ofHom
  (NodalFiber.punctureCoefficientRingMap f c₁ c₀ hc opposite))
local notation "F" => Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f))
local notation "a₀" => initialTerminalArithmeticPunctureIso
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "a₁" => initialTerminalArithmeticPunctureIso
  π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite

/-- Both full initial-to-terminal puncture maps retain the original Laurent coefficient map. -/
@[reassoc] theorem initialTerminalArithmeticPunctureIso_restriction :
    F ≫ (a₁).hom = (a₀).hom ≫ P := by
  let _ : IsOpenImmersion i₁ := IsOpenImmersion.of_isLocalization δ₁
  apply (cancel_mono i₁).mp
  rw [Category.assoc, initialTerminalArithmeticPunctureIso_boundary,
    Category.assoc, NodalFiber.punctureCoefficientRingMap_square,
    ← Category.assoc, initialTerminalArithmeticPunctureIso_boundary]
  exact initialTerminalArithmeticNodeEvaluation_restriction_square
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite

/-- The inverse initial parameter comparison preserves the same original quotient projection. -/
@[reassoc] theorem initialTerminalArithmeticPunctureIso_inv_restriction :
    P ≫ (a₁).inv = (a₀).inv ≫ F := by
  have h := initialTerminalArithmeticPunctureIso_restriction
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
  have he := congrArg (fun g ↦ (a₀).inv ≫ g ≫ (a₁).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using he.symm

end FLT.Mazur.WeierstrassModificationX
