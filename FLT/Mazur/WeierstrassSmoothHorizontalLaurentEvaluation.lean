/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalResidueCoordinates

/-!
# Laurent evaluation in the two-factor residue product

The conic and smooth units remain independent. Evaluating the conic Laurent
coordinate at their product gives the first branch character, while using
the inverse smooth unit gives the opposite character.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "C" => SmoothHorizontalResidueRing D
local notation "j" => smoothHorizontalResidueConic D

/-- The independent conic Laurent coordinate is a unit on the residue product. -/
def smoothHorizontalConicUnit : Cˣ :=
  ((LaurentPolynomial.isUnit_T (R := K) 1).map (j).toRingHom).unit

/-- The conic unit is the original positive Laurent generator in the first factor. -/
theorem smoothHorizontalConicUnit_val :
    (smoothHorizontalConicUnit D : C) = j (LaurentPolynomial.T 1) := IsUnit.unit_spec _

/-- Evaluate the conic Laurent parameter at an arbitrary unit of the residue product. -/
def smoothHorizontalLaurentEvaluation (q : Cˣ) : L →ₐ[K] C :=
  { LaurentPolynomial.eval₂ (algebraMap K C) q with
    commutes' := fun r => LaurentPolynomial.eval₂_C _ _ r }

/-- Laurent evaluation preserves every residue coefficient. -/
theorem smoothHorizontalLaurentEvaluation_C (q : Cˣ) (r : K) :
    smoothHorizontalLaurentEvaluation D q (LaurentPolynomial.C r) = algebraMap K C r :=
  LaurentPolynomial.eval₂_C _ _ _

/-- Laurent evaluation records all integral powers of the chosen unit. -/
theorem smoothHorizontalLaurentEvaluation_T (q : Cˣ) (n : ℤ) :
    smoothHorizontalLaurentEvaluation D q (LaurentPolynomial.T n) = (q ^ n : Cˣ) :=
  LaurentPolynomial.eval₂_T _ _ _

/-- The first action scale is exactly a times the product of the two Laurent parameters. -/
theorem smoothHorizontalLaurentEvaluation_first (r : K) :
    smoothHorizontalLaurentEvaluation D
      (smoothHorizontalTangentUnit D * smoothHorizontalConicUnit D)
      (LaurentPolynomial.C r * LaurentPolynomial.T 1) =
    (smoothHorizontalTangentUnit D : C) * j
      (LaurentPolynomial.C r * LaurentPolynomial.T 1) := by
  rw [map_mul, smoothHorizontalLaurentEvaluation_C, smoothHorizontalLaurentEvaluation_T,
    zpow_one, Units.val_mul, smoothHorizontalConicUnit_val, map_mul]
  change algebraMap K C r * ((smoothHorizontalTangentUnit D : C) * j _) =
    (smoothHorizontalTangentUnit D : C) * (j (algebraMap K L r) * j _)
  rw [AlgHom.commutes]
  ring

/-- The opposite action scale keeps its sign and the inverse smooth character. -/
theorem smoothHorizontalLaurentEvaluation_second (r : K) :
    smoothHorizontalLaurentEvaluation D
      ((smoothHorizontalTangentUnit D)⁻¹ * smoothHorizontalConicUnit D)
      (-LaurentPolynomial.C r * LaurentPolynomial.T 1) =
    (↑(smoothHorizontalTangentUnit D)⁻¹ : C) * j
      (-LaurentPolynomial.C r * LaurentPolynomial.T 1) := by
  rw [map_mul, map_neg, smoothHorizontalLaurentEvaluation_C,
    smoothHorizontalLaurentEvaluation_T, zpow_one, Units.val_mul,
    smoothHorizontalConicUnit_val, map_mul, map_neg]
  change -algebraMap K C r * ((↑(smoothHorizontalTangentUnit D)⁻¹ : C) * j _) =
    (↑(smoothHorizontalTangentUnit D)⁻¹ : C) * (-(j (algebraMap K L r)) * j _)
  rw [AlgHom.commutes]
  ring

end FLT.Mazur.WeierstrassIntegralChart
