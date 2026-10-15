/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticCoordinates

/-!
# Compatibility of the original resolved arithmetic coordinates

The actual quotient-ring restrictions define the stage maps. The original
coordinate sections commute with those maps through the canonical line
comparison. The retained zero is the original cubic zero at every order.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.WeierstrassDividedDepth
open FCurve WeierstrassIntegralChart PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- The actual adjacent restriction between the original resolved arithmetic stages. -/
def finiteGlobalArithmeticRestriction (m : ℕ) :
    finiteGlobalArithmeticStage hπ data j hj m ⟶
      finiteGlobalArithmeticStage hπ data j hj (m + 1) :=
  Limits.pullback.lift (finiteGlobalArithmeticProjection hπ data j hj m)
    (finiteGlobalArithmeticStructure hπ data j hj m ≫ baseRestriction R π m) (by
      rw [Category.assoc, baseRestriction_toIntegral]
      exact Limits.pullback.condition)

/-- Arithmetic restriction retains the original resolved-model projection. -/
@[reassoc] theorem finiteGlobalArithmeticRestriction_projection (m : ℕ) :
    finiteGlobalArithmeticRestriction hπ data j hj m ≫
        finiteGlobalArithmeticProjection hπ data j hj (m + 1) =
      finiteGlobalArithmeticProjection hπ data j hj m :=
  Limits.pullback.lift_fst _ _ _

/-- The arithmetic transition uses precisely the original quotient coefficient restriction. -/
@[reassoc] theorem finiteGlobalArithmeticRestriction_structure (m : ℕ) :
    finiteGlobalArithmeticRestriction hπ data j hj m ≫
        finiteGlobalArithmeticStructure hπ data j hj (m + 1) =
      finiteGlobalArithmeticStructure hπ data j hj m ≫ baseRestriction R π m :=
  Limits.pullback.lift_snd _ _ _

/-- Every arithmetic transition commutes with contraction to the same original cubic. -/
@[reassoc] theorem finiteGlobalArithmeticRestriction_toCubic (m : ℕ) :
    finiteGlobalArithmeticRestriction hπ data j hj m ≫
        finiteGlobalArithmeticToCubic hπ data j hj (m + 1) =
      finiteGlobalArithmeticToCubic hπ data j hj m := by
  rw [finiteGlobalArithmeticToCubic, finiteGlobalArithmeticRestriction_projection_assoc]
  rfl

/-- The original coordinate lines have their actual adjacent restriction comparison. -/
def finiteGlobalArithmeticCoordinateIso (m : ℕ) :
    (pullback (finiteGlobalArithmeticRestriction hπ data j hj m)).obj
      (finiteGlobalArithmeticCoordinateLine hπ data j hj (m + 1)) ≅
        finiteGlobalArithmeticCoordinateLine hπ data j hj m :=
  pullbackStageIso _ _ _ (finiteGlobalArithmeticRestriction_toCubic hπ data j hj m)
    (integralCoordinateLine W)

/-- The constructed coordinates form an actual compatible arithmetic section system. -/
theorem finiteGlobalArithmeticCoordinateSection_restrict (m : ℕ) (i : Fin 3) :
    (finiteGlobalArithmeticCoordinateIso hπ data j hj m).hom.app ⊤
      (pullGlobal (finiteGlobalArithmeticRestriction hπ data j hj m) _
        (finiteGlobalArithmeticCoordinateSection hπ data j hj (m + 1) i)) =
      finiteGlobalArithmeticCoordinateSection hπ data j hj m i :=
  pullbackStageIso_globalSection _ _ _
    (finiteGlobalArithmeticRestriction_toCubic hπ data j hj m)
    (integralCoordinateLine W) (integralCoordinateSection W i)

/-- Each arithmetic coordinate line is the restriction of the original resolved line. -/
def finiteGlobalArithmeticCoordinateProjectionIso (m : ℕ) :
    (pullback (finiteGlobalArithmeticProjection hπ data j hj m)).obj
      (finiteGlobalCoordinateLine hπ data j hj) ≅
        finiteGlobalArithmeticCoordinateLine hπ data j hj m :=
  pullbackStageIso _ _ _ rfl (integralCoordinateLine W)

/-- Restriction of each original integral section gives the constructed arithmetic section. -/
theorem finiteGlobalArithmeticCoordinateSection_projection (m : ℕ) (i : Fin 3) :
    (finiteGlobalArithmeticCoordinateProjectionIso hπ data j hj m).hom.app ⊤
      (pullGlobal (finiteGlobalArithmeticProjection hπ data j hj m) _
        (finiteGlobalCoordinateSection hπ data j hj i)) =
      finiteGlobalArithmeticCoordinateSection hπ data j hj m i :=
  pullbackStageIso_globalSection _ _ _ rfl
    (integralCoordinateLine W) (integralCoordinateSection W i)

/-- The original zero section is retained at every arithmetic order. -/
@[reassoc] theorem finiteGlobalArithmeticZero_toCubic (m : ℕ) :
    finiteGlobalBaseChangeZero hπ data j hj (baseToIntegral R π m) ≫
        finiteGlobalArithmeticToCubic hπ data j hj m =
      baseToIntegral R π m ≫ integralCurveZero W := by
  rw [finiteGlobalArithmeticToCubic, finiteGlobalBaseChangeZero,
    finiteGlobalArithmeticProjection, Limits.pullback.lift_fst_assoc,
    Category.assoc, finiteGlobalZero_contraction]

end FLT.Mazur.WeierstrassDividedDepth
