/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorCoefficientMap
public import FLT.Mazur.WeierstrassDividedArithmeticTensorProjection
public import FLT.Mazur.WeierstrassDividedArithmeticCoordinateTransition

/-!
# Quotient restriction on every original arithmetic tensor chart

The full initial, terminal, infinity and arbitrarily retained tensor charts
commute with the actual global arithmetic restriction. Retained depths use
one fixed global stage on both sides of the square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "f" => restriction R π m

/-- The complete initial tensor chart commutes with the original quotient map. -/
@[reassoc] theorem finiteArithmeticInitialTensorChart_restriction (k : ℕ) (hk : k ≤ n) :
    TensorCoefficientMap.spectrum f ≫
      finiteArithmeticInitialTensorChart hπ data (m + 1) k hk =
        finiteArithmeticInitialTensorChart hπ data m k hk ≫
          finiteGlobalArithmeticRestriction hπ data k hk m := by
  apply TensorCoefficientMap.square_of_projections
      f (finiteGlobalStructure hπ data k hk) _
  · exact finiteArithmeticInitialTensorChart_projection hπ data (m + 1) k hk
  · exact finiteArithmeticInitialTensorChart_projection hπ data m k hk
  · exact finiteArithmeticInitialTensorChart_structure hπ data (m + 1) k hk
  · exact finiteArithmeticInitialTensorChart_structure hπ data m k hk
  · exact finiteGlobalArithmeticRestriction_projection hπ data k hk m
  · exact finiteGlobalArithmeticRestriction_structure hπ data k hk m

/-- The whole terminal tensor chart uses the same original global quotient restriction. -/
@[reassoc] theorem finiteArithmeticDividedTensorChart_restriction (k : ℕ) (hk : k ≤ n) :
    TensorCoefficientMap.spectrum f ≫
      finiteArithmeticDividedTensorChart hπ data (m + 1) k hk =
        finiteArithmeticDividedTensorChart hπ data m k hk ≫
          finiteGlobalArithmeticRestriction hπ data k hk m := by
  apply TensorCoefficientMap.square_of_projections
      f (finiteGlobalStructure hπ data k hk) _
  · exact finiteArithmeticDividedTensorChart_projection hπ data (m + 1) k hk
  · exact finiteArithmeticDividedTensorChart_projection hπ data m k hk
  · exact finiteArithmeticDividedTensorChart_structure hπ data (m + 1) k hk
  · exact finiteArithmeticDividedTensorChart_structure hπ data m k hk
  · exact finiteGlobalArithmeticRestriction_projection hπ data k hk m
  · exact finiteGlobalArithmeticRestriction_structure hπ data k hk m

/-- Every retained tensor chart commutes with restriction at its actual later stage. -/
@[reassoc] theorem finiteArithmeticOlderTensorChart_restriction
    (a : ℕ) (ha : a + 1 ≤ n) (r : ℕ) (hr : a + 1 + r ≤ n) :
    TensorCoefficientMap.spectrum f ≫
      finiteArithmeticOlderTensorChart hπ data (m + 1) a ha r hr =
        finiteArithmeticOlderTensorChart hπ data m a ha r hr ≫
          finiteGlobalArithmeticRestriction hπ data (a + 1 + r) hr m := by
  apply TensorCoefficientMap.square_of_projections
      f (finiteGlobalStructure hπ data (a + 1 + r) hr) _
  · exact finiteArithmeticOlderTensorChart_projection hπ data (m + 1) a ha r hr
  · exact finiteArithmeticOlderTensorChart_projection hπ data m a ha r hr
  · exact finiteArithmeticOlderTensorChart_structure hπ data (m + 1) a ha r hr
  · exact finiteArithmeticOlderTensorChart_structure hπ data m a ha r hr
  · exact finiteGlobalArithmeticRestriction_projection hπ data (a + 1 + r) hr m
  · exact finiteGlobalArithmeticRestriction_structure hπ data (a + 1 + r) hr m

/-- Infinity commutes with the quotient without any stage-index change. -/
@[reassoc] theorem arithmeticTensorAtlas_infinity_restriction (k : ℕ) (hk : k ≤ n) :
    TensorCoefficientMap.spectrum f ≫ arithmeticTensorAtlasMap hπ data (m + 1) k hk 0 =
      arithmeticTensorAtlasMap hπ data m k hk 0 ≫
        finiteGlobalArithmeticRestriction hπ data k hk m := by
  apply TensorCoefficientMap.square_of_projections
      f (finiteGlobalStructure hπ data k hk) (finiteInfinityChart hπ data k hk)
  · exact arithmeticTensorAtlas_infinity_projection hπ data (m + 1) k hk
  · exact arithmeticTensorAtlas_infinity_projection hπ data m k hk
  · exact arithmeticTensorAtlas_infinity_structure hπ data (m + 1) k hk
  · exact arithmeticTensorAtlas_infinity_structure hπ data m k hk
  · exact finiteGlobalArithmeticRestriction_projection hπ data k hk m
  · exact finiteGlobalArithmeticRestriction_structure hπ data k hk m

/-- A fixed retained depth has the same quotient square at any containing stage. -/
@[reassoc] theorem arithmeticRetainedTensorChart_restriction
    (k : ℕ) (hk : k ≤ n) (a : ℕ) (ha : a < k) :
    TensorCoefficientMap.spectrum f ≫ arithmeticRetainedTensorChart hπ data (m + 1) k hk a ha =
      arithmeticRetainedTensorChart hπ data m k hk a ha ≫
        finiteGlobalArithmeticRestriction hπ data k hk m := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt ha)
  have hk' : k = a + 1 + r := by omega
  subst k
  rw [arithmeticRetainedTensorChart_eq hπ data (m + 1) (a + 1 + r) hk a ha r hk,
    arithmeticRetainedTensorChart_eq hπ data m (a + 1 + r) hk a ha r hk]
  exact finiteArithmeticOlderTensorChart_restriction hπ data m a (by omega) r hk

end FLT.Mazur.WeierstrassDividedDepth
