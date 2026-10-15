/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticNodeCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticCoordinateTransition
public import FLT.Mazur.WeierstrassSuccessiveArithmeticProjection
public import FLT.Mazur.WeierstrassSuccessiveArithmeticOppositeRestrictionSquare

/-!
# The actual global arithmetic branch restriction squares

The integral coordinate projection and the original quotient structure
identify the full global square. Both constructed polygon node branches
therefore commute with the original global arithmetic restriction maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassIntegralChart WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "e" => WeierstrassSuccessiveX.baseChangeEquiv W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q
local notation "c" => WeierstrassSuccessiveX.arithmeticNodeChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6

local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

/-- The whole arithmetic successive chart retains its original integral atlas projection. -/
@[reassoc] theorem finiteArithmeticSuccessiveChart_projection :
    finiteArithmeticSuccessiveChart hπ data j hj m ≫
      finiteGlobalArithmeticProjection hπ data (j + 1) hj m =
        Spec.map (CommRingCat.ofHom (coefficientMap W (π ^ (start + j)) π
          (Data.b3 d) (Data.b4 d) (Data.b6 d) Q).toRingHom) ≫
          finiteAtlasMap hπ data E₀ (j + 1) hj 1 ≫
            finiteLocalChart hπ data (j + 1) hj := by
  change (Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
    globalSuccessiveTensorChart hπ data Q j hj ≫
      (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1) hj)).hom) ≫
        pullback.fst (finiteGlobalStructure hπ data (j + 1) hj) q = _
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, globalSuccessiveTensorChart,
    finiteLocalTensorEmbedding_square, finiteSuccessiveTensorChart,
    TensorOpenChart.chart_snd_assoc, baseChangeEquiv_spec_projection_assoc]

/-- The actual successive atlas comparison commutes with the full global restriction. -/
@[reassoc] theorem finiteArithmeticSuccessiveChart_restriction_square :
    arithmeticSuccessiveRestriction R π m W (π ^ (start + j))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) ≫
        finiteArithmeticSuccessiveChart hπ data j hj (m + 1) =
      finiteArithmeticSuccessiveChart hπ data j hj m ≫
        finiteGlobalArithmeticRestriction hπ data (j + 1) hj m := by
  apply pullback.hom_ext
  · change _ ≫ finiteGlobalArithmeticProjection hπ data (j + 1) hj (m + 1) =
      _ ≫ finiteGlobalArithmeticProjection hπ data (j + 1) hj (m + 1)
    simp only [Category.assoc, finiteArithmeticSuccessiveChart_projection,
      arithmeticSuccessiveRestriction_projection_assoc,
      finiteGlobalArithmeticRestriction_projection]
  · change _ ≫ finiteGlobalArithmeticStructure hπ data (j + 1) hj (m + 1) =
      _ ≫ finiteGlobalArithmeticStructure hπ data (j + 1) hj (m + 1)
    simp only [Category.assoc, finiteArithmeticSuccessiveChart_structure,
      arithmeticSuccessiveRestriction_structure,
      finiteGlobalArithmeticRestriction_structure, finiteArithmeticSuccessiveChart_structure_assoc]

/-- The constructed small polygon branch commutes with the original global restriction. -/
@[reassoc] theorem finiteArithmeticNodeChart_restriction_square :
    arithmeticPolygonNodeRestriction R π m ≫
      finiteArithmeticNodeChart hπ data j hj (m + 1) ha hs h2 h3 h4 h6 =
    finiteArithmeticNodeChart hπ data j hj m ha hs h2 h3 h4 h6 ≫
      finiteGlobalArithmeticRestriction hπ data (j + 1) hj m := by
  change arithmeticPolygonNodeRestriction R π m ≫
    arithmeticNodeChart π (m + 1) W (π ^ (start + j))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 ≫
        finiteArithmeticSuccessiveChart hπ data j hj (m + 1) =
      (c ≫ finiteArithmeticSuccessiveChart hπ data j hj m) ≫ _
  rw [← Category.assoc, arithmeticNodeChart_restriction_square,
    Category.assoc, finiteArithmeticSuccessiveChart_restriction_square, Category.assoc]

/-- The constructed opposite polygon branch uses the same original global restriction. -/
@[reassoc] theorem finiteArithmeticOppositeNodeChart_restriction_square :
    arithmeticPolygonNodeRestriction R π m ≫
      finiteArithmeticOppositeNodeChart hπ data j hj (m + 1) ha hs h2 h3 h4 h6 =
    finiteArithmeticOppositeNodeChart hπ data j hj m ha hs h2 h3 h4 h6 ≫
      finiteGlobalArithmeticRestriction hπ data (j + 1) hj m := by
  change arithmeticPolygonNodeRestriction R π m ≫
    arithmeticOppositeNodeChart π (m + 1) W (π ^ (start + j))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 ≫
        finiteArithmeticSuccessiveChart hπ data j hj (m + 1) =
      (arithmeticOppositeNodeChart π m W (π ^ (start + j))
        (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 ≫
          finiteArithmeticSuccessiveChart hπ data j hj m) ≫ _
  rw [← Category.assoc, arithmeticOppositeNodeChart_restriction_square,
    Category.assoc, finiteArithmeticSuccessiveChart_restriction_square, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
