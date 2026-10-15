/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoefficientTransport
public import FLT.Mazur.WeierstrassDilatationArithmeticSmoothingRestriction

/-!
# Explicit original quotient restriction on the full terminal cubic

The target is the original lower-order equation. Coefficient identities are
transported explicitly, retaining both original coordinates and all constants.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages
variable (R : Type*) [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => AlgHom.toRingHom (restriction R π m)

/-- The whole original Weierstrass coefficient tuple restricts to the lower-order tuple. -/
theorem arithmeticTerminalCurve_restriction : (W.map q₁).map f = W.map q₀ := by
  rw [WeierstrassCurve.map_map]
  exact congrArg W.map (restriction R π m).comp_algebraMap

/-- Restrict the full original cubic to the explicitly identified lower-order equation. -/
def arithmeticTerminalCoefficientMap : ExtendedCoordinate W s b3 b4 b6 Q₁ →+*
    ExtendedCoordinate W s b3 b4 b6 Q₀ :=
  coefficientRingMapTo f (W.map q₁) (q₁ s) (q₁ b3) (q₁ b4) (q₁ b6)
    (W.map q₀) (q₀ s) (q₀ b3) (q₀ b4) (q₀ b6)
    (arithmeticTerminalCurve_restriction R π m W) ((restriction R π m).commutes s)
    ((restriction R π m).commutes b3) ((restriction R π m).commutes b4)
    ((restriction R π m).commutes b6)

/-- The actual arithmetic restriction retains the original horizontal coordinate. -/
theorem arithmeticTerminalCoefficientMap_x :
    arithmeticTerminalCoefficientMap R π m W s b3 b4 b6
      (x (W.map q₁) (q₁ s) (q₁ b3) (q₁ b4) (q₁ b6)) =
      x (W.map q₀) (q₀ s) (q₀ b3) (q₀ b4) (q₀ b6) := coefficientRingMapTo_x ..

/-- The actual arithmetic restriction retains the original vertical coordinate. -/
theorem arithmeticTerminalCoefficientMap_y :
    arithmeticTerminalCoefficientMap R π m W s b3 b4 b6
      (y (W.map q₁) (q₁ s) (q₁ b3) (q₁ b4) (q₁ b6)) =
      y (W.map q₀) (q₀ s) (q₀ b3) (q₀ b4) (q₀ b6) := coefficientRingMapTo_y ..

/-- All arithmetic scalars follow the original quotient map. -/
theorem arithmeticTerminalCoefficientMap_scalar (a : Q₁) :
    arithmeticTerminalCoefficientMap R π m W s b3 b4 b6 (algebraMap Q₁ _ a) =
      algebraMap Q₀ _ (f a) := coefficientRingMapTo_algebraMap ..

end FLT.Mazur.WeierstrassDilatation
