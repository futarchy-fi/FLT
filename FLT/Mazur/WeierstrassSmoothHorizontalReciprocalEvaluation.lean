/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonReciprocalEvaluation
public import FLT.Mazur.WeierstrassSmoothHorizontalLaurentEvaluation
public import FLT.Mazur.LaurentUnitPoints

/-!
# Actual smooth residue inputs in reciprocal line coordinates

The independent conic input becomes the signed reciprocal unit. The two
actual output evaluations have the reversed characters on the next lines.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "J" => smoothHorizontalResidueConic D
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D

/-- The independent original conic map evaluates at its actual Laurent unit. -/
theorem smoothHorizontalConicUnit_evaluation :
    smoothHorizontalLaurentEvaluation D z = J := by
  have h := LaurentUnitPoints.evalUnit_pointUnit J
  have hu : LaurentUnitPoints.pointUnit J = z := by
    apply Units.ext
    exact (smoothHorizontalConicUnit_val D).symm
  rw [hu] at h
  exact h

/-- The actual reciprocal parameter on a next line, retaining its signed scale. -/
def smoothHorizontalReciprocalUnit (a : (ResidueField R)ˣ) : Cˣ :=
  Units.map (algebraMap K C) a * (smoothHorizontalConicUnit D)⁻¹

variable (a : (ResidueField R)ˣ)
local notation "ρ" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal a)))
local notation "q" => smoothHorizontalReciprocalUnit D a

/-- The complete original input followed by reciprocity evaluates at the reciprocal unit. -/
theorem smoothHorizontalReciprocal_input :
    Spec.map (CommRingCat.ofHom (J).toRingHom) ≫ ρ =
      Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D q).toRingHom) := by
  rw [← smoothHorizontalConicUnit_evaluation, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (PolygonScaledReciprocal.evaluation_comp_reciprocal a z)

/-- The first actual conic output has inverse character on its reciprocal line. -/
theorem smoothHorizontalReciprocal_firstOutput :
    Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ * z)).toRingHom) ≫ ρ =
      Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ⁻¹ * q)).toRingHom) := by
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (PolygonScaledReciprocal.evaluation_reciprocal_mul a τ z)

/-- The opposite actual output has positive character on the opposite signed line. -/
theorem smoothHorizontalReciprocal_secondOutput :
    Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).toRingHom) ≫ ρ =
      Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ * q)).toRingHom) := by
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (PolygonScaledReciprocal.evaluation_reciprocal_inv_mul a τ z)

end FLT.Mazur.WeierstrassIntegralChart
