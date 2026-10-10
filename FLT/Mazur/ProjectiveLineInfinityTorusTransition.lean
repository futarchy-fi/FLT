/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineInfinityTorusCover
public import FLT.Mazur.WeierstrassSlopeLaurentGeometry

/-!
# The exact slope transition into the translated infinity torus

The full original slope map T=(v+a)/v gives w=1/v in the standard right
projective-line chart. Both equalities hold on every function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a : Kˣ)
local notation "P" => SlopeOpen (a : K)
local notation "z" => slopeZ (a : K)
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial (a : K))
local notation "m" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (slopeLaurentMap a)))

/-- The original slope parameter restricted to the standard projective-line overlap. -/
def infinitySlopeStandardMap : K[T;T⁻¹] →+* P :=
  LaurentPolynomial.eval₂ (algebraMap K P) (slope_units (a : K)).1.unit

/-- The standard overlap still has the original slope coordinate v. -/
theorem infinitySlopeStandardMap_T : infinitySlopeStandardMap a (LaurentPolynomial.T 1) =
    z := by
  rw [infinitySlopeStandardMap, LaurentPolynomial.eval₂_T]
  simpa only [zpow_one] using (slope_units (a : K)).1.unit_spec

/-- The right-chart coordinate on the standard overlap is the inverse of v. -/
theorem infinitySlopeStandardMap_inv :
    infinitySlopeStandardMap a (LaurentPolynomial.T (-1)) =
      ↑(slope_units (a : K)).1.unit⁻¹ := by
  rw [infinitySlopeStandardMap, LaurentPolynomial.eval₂_T]
  simp only [zpow_neg_one]

/-- The original ratio map gives exactly 1/v in the translated right coordinate. -/
theorem infinitySlope_right_coordinate :
    slopeLaurentMap a (infinityTorusMap a X) = ↑(slope_units (a : K)).1.unit⁻¹ := by
  rw [infinityTorusMap_X, map_mul]
  rw [show slopeLaurentMap a (LaurentPolynomial.C (↑a⁻¹ : K)) =
    algebraMap K P (↑a⁻¹ : K) from (slopeLaurentMap a).commutes _]
  rw [slopeLaurentMap_sub_one, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- The full slope open maps to the standard Laurent overlap. -/
def infinitySlopeToStandard : Spec (.of P) ⟶ overlap K :=
  Spec.map (CommRingCat.ofHom (infinitySlopeStandardMap a))

/-- The left leg retains every function of the original affine slope line. -/
@[reassoc] theorem infinitySlopeToStandard_left :
    infinitySlopeToStandard a ≫ overlapLeft K = s := by
  rw [infinitySlopeToStandard, overlapLeft, ← Spec.map_comp]
  change Spec.map _ = Spec.map _
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change infinitySlopeStandardMap a (Polynomial.toLaurent (C r)) =
      algebraMap K[X] P (C r)
    rw [Polynomial.toLaurent_C, infinitySlopeStandardMap, LaurentPolynomial.eval₂_C]
    exact IsScalarTower.algebraMap_apply K K[X] P r
  · change infinitySlopeStandardMap a (Polynomial.toLaurent X) = z
    rw [Polynomial.toLaurent_X, infinitySlopeStandardMap_T]

/-- The right leg is the original ratio map followed by the full translated torus inclusion. -/
@[reassoc] theorem infinitySlopeToStandard_right :
    infinitySlopeToStandard a ≫ overlapRight K = m ≫ infinityTorusToRight a := by
  rw [infinitySlopeToStandard, overlapRight, inversion_hom, overlapLeft,
    infinityTorusToRight, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change infinitySlopeStandardMap a
      (LaurentPolynomial.invert (Polynomial.toLaurent (C r))) =
        slopeLaurentMap a (infinityTorusMap a (C r))
    rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_C,
      infinitySlopeStandardMap, LaurentPolynomial.eval₂_C]
    exact ((slopeLaurentMap a).commutes r).symm.trans
      (congrArg (slopeLaurentMap a) ((infinityTorusMap a).commutes r).symm)
  · change infinitySlopeStandardMap a
      (LaurentPolynomial.invert (Polynomial.toLaurent X)) =
        slopeLaurentMap a (infinityTorusMap a X)
    rw [transition_X, infinitySlopeStandardMap_inv, infinitySlope_right_coordinate]

/-- The canonical original slope transition commutes in the full projective line. -/
@[reassoc] theorem infinityTorus_slope_condition :
    s ≫ left K = m ≫ infinityTorusChart a := by
  rw [← infinitySlopeToStandard_left a, Category.assoc, overlap_condition,
    ← Category.assoc, infinitySlopeToStandard_right, Category.assoc, infinityTorusChart]

end FLT.Mazur.ProjectiveLine
