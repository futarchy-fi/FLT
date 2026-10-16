/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialTerminalNodeBoundary
public import FLT.Mazur.WeierstrassDilatationArithmeticTensorNormalization
public import FLT.Mazur.WeierstrassModificationXArithmeticTerminalLaurentRestriction

/-!
# Full normalized initial-terminal evaluations commute with arithmetic restriction

Both original initial Boolean boundary maps retain every original Laurent function
and every corrected node coordinate across consecutive quotient orders.
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
local notation "e₀" => WeierstrassDilatation.arithmeticTerminalNodeEquiv π m W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "e₁" => WeierstrassDilatation.arithmeticTerminalNodeEquiv π (m + 1) W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "v₀" => arithmeticInitialLaurentSlope
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "hv₀" => arithmeticInitialLaurentSlope_equation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "v₁" => arithmeticInitialLaurentSlope
  π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "hv₁" => arithmeticInitialLaurentSlope_equation
  π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "G₀" => tensorInitialTerminalLaurent W s b3 b4 b6 Q₀ v₀ hv₀
local notation "G₁" => tensorInitialTerminalLaurent W s b3 b4 b6 Q₁ v₁ hv₁

/-- The two full corrected node evaluations retain the original Laurent coefficient map. -/
theorem initialTerminalArithmeticNodeEvaluation_restriction :
    (PolygonScalingNaturality.coeffMap f).comp (E₁).toRingHom =
      (E₀).toRingHom.comp N := by
  apply RingHom.ext
  intro z
  change PolygonScalingNaturality.coeffMap f (G₁ ((e₁).symm z)) =
    G₀ ((e₀).symm (N z))
  have hg := DFunLike.congr_fun
    (arithmeticInitialTerminalLaurent_restriction R π m W s
      b3 b4 b6 ha hs h2 h3 h4 h6 opposite) ((e₁).symm z)
  have hn := DFunLike.congr_fun
    (WeierstrassDilatation.arithmeticTerminalNodeEquiv_symm_restriction R π m W s
      b3 b4 b6 ha hs h2 h4 h6) z
  exact hg.trans (congrArg G₀ hn)

/-- The original Laurent and full node coefficient projections form a scheme square. -/
@[reassoc] theorem initialTerminalArithmeticNodeEvaluation_restriction_square :
    Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f)) ≫
      Spec.map (CommRingCat.ofHom (E₁).toRingHom) =
    Spec.map (CommRingCat.ofHom (E₀).toRingHom) ≫ Spec.map (CommRingCat.ofHom N) := by
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g))
    (initialTerminalArithmeticNodeEvaluation_restriction
      π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)

end FLT.Mazur.WeierstrassModificationX
