/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedClosingIso
public import FLT.Mazur.WeierstrassRetainedEdgeUnitNaturality

/-!
# Restriction of the original full retained closing parameter

The actual quotient, recursive scale and full root correction all restrict.
Consequently the complete closing substitution and its inverse form compatible
families at every arithmetic order, without replacing the source overlaps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n) (a : Fin k)
local notation "Q" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "F" => ringMap f (parameter R π (m + 1))
  (parameter R π m) (restriction_parameter R π m)
local notation "V" => arithmeticRetainedFullCorrection data H m k hk a
local notation "V₁" => arithmeticRetainedFullCorrection data H (m + 1) k hk a
local notation "q" => arithmeticStartOneQuotient W H.a1_unit π m
local notation "q₁" => arithmeticStartOneQuotient W H.a1_unit π (m + 1)
local notation "v" => arithmeticRetainedClosingUnit data H m k hk a
local notation "v₁" => arithmeticRetainedClosingUnit data H (m + 1) k hk a
local notation "ρ" => Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f))
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) v)))
local notation "B₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q₁) v₁)))

/-- The reciprocal outgoing unit retains the entire correction under restriction. -/
theorem arithmeticRetainedClosingUnit_restriction :
    Units.map (PolygonScalingNaturality.coeffMap f).toMonoidHom v₁ = v := by
  have hu : Units.map (F).toMonoidHom
      (retainedScaledCorrectionUnit (parameter R π (m + 1))
        (retainedDepthScale q₁ 1 a.val) V₁) =
      retainedScaledCorrectionUnit (parameter R π m) (retainedDepthScale q 1 a.val) V := by
    rw [retainedScaledCorrectionUnit_coefficients f
      (parameter R π (m + 1)) (parameter R π m) (restriction_parameter R π m)
      V₁ V (arithmeticRetainedFullCorrection_restriction data H m k hk a),
      retainedDepthScale_map, map_one, arithmeticStartOneQuotient_restriction]
  unfold arithmeticRetainedClosingUnit
  rw [map_inv, retainedFixedEdgeUnit_coefficients f _ _ (restriction_parameter R π m)
    q₁ _ _ hu, arithmeticStartOneQuotient_restriction]

/-- The whole original retained parameter map commutes with the quotient arrows. -/
@[reassoc] theorem arithmeticRetainedClosingParameter_restriction :
    ρ ≫ B₁ = B ≫ ρ := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g))
    (LaurentUnitPoints.evalUnit_coefficients f v₁ v
      (arithmeticRetainedClosingUnit_restriction data H m k hk a))

/-- Uniqueness of inverses makes the constructed retained inverse compatible as well. -/
@[reassoc] theorem arithmeticRetainedClosingParameter_inv_restriction :
    ρ ≫ inv B₁ = inv B ≫ ρ := by
  apply (cancel_mono B₁).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    Category.assoc, arithmeticRetainedClosingParameter_restriction,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
