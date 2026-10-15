/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteCoherence
public import FLT.Mazur.PolygonCompleteIdentityFiniteUnits
public import FLT.Mazur.LaurentPairCoefficientNaturality

/-!
# The actual original multiplication coordinates form a compatible finite system

Both Laurent inputs commute with the original coefficient restrictions.
Original multiplication and its full coordinate lift therefore commute with
successive finite orders, without an assumed Laurent multiplication formula.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "D" => Spec.map (CommRingCat.ofHom (coeffMap (coeffMap
  (AlgHom.toRingHom (restriction K m)))))
local notation "L" => Spec.map (CommRingCat.ofHom
  (coeffMap (AlgHom.toRingHom (restriction K m))))

/-- The actual original pair retains both inputs under an adjacent coefficient restriction. -/
@[reassoc] theorem completeIdentityFinitePair_restriction :
    (D) ≫ completeIdentityFinitePair K n h i (m + 1) =
      completeIdentityFinitePair K n h i m := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityFinitePair_fst, completeIdentityFinitePair_fst]
    change (D) ≫ Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.C : (Ring K (m + 1))[T;T⁻¹] →+*
        (Ring K (m + 1))[T;T⁻¹][T;T⁻¹])) ≫
        completeIdentityStageTorus K n h i (m + 1) =
      Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.C : (Ring K m)[T;T⁻¹] →+* (Ring K m)[T;T⁻¹][T;T⁻¹])) ≫
        completeIdentityStageTorus K n h i m
    rw [LaurentPairCoefficientNaturality.firstProjection_spec_assoc
      (restriction K m).toRingHom, completeIdentityStageTorus_restriction K n h i m]
  · rw [Category.assoc, completeIdentityFinitePair_snd, completeIdentityFinitePair_snd,
      LaurentPairCoefficientNaturality.secondProjection_spec_assoc (restriction K m).toRingHom,
      completeIdentityStageTorus_restriction K n h i m]

/-- Original multiplication is compatible with the actual adjacent finite inputs. -/
@[reassoc] theorem completeIdentityFiniteOriginalMul_restriction :
    (D) ≫ completeIdentityFiniteOriginalMul K n h i (m + 1) =
      completeIdentityFiniteOriginalMul K n h i m := by
  rw [completeIdentityFiniteOriginalMul, completeIdentityFiniteOriginalMul,
    completeIdentityFinitePair_restriction_assoc]

/-- The full Laurent coordinate law commutes with the original adjacent coefficient quotient. -/
@[reassoc] theorem completeIdentityFiniteMulCoordinates_restriction :
    (D) ≫ completeIdentityFiniteMulCoordinates K n h i (m + 1) =
      completeIdentityFiniteMulCoordinates K n h i m ≫ (L) := by
  apply (cancel_mono (completeIdentityStageTorus K n h i (m + 1))).mp
  simp only [Category.assoc, completeIdentityFiniteMulCoordinates_original,
    completeIdentityFiniteOriginalMul_restriction, completeIdentityStageTorus_restriction K n h i m]

end FLT.Mazur.PolygonInfinitesimalStages
