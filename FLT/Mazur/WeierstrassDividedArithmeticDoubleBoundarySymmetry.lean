/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairDoubleBoundarySymmetry
public import FLT.Mazur.WeierstrassDividedArithmeticDoubleBoundary

/-!
# Both arithmetic boundary changes commute

The original indexed chart embeddings detect equality of the entire target
pair, so swapping the factors and reversing change order gives the same map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j ≤ n) (a b c d : Fin (j + 3))
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
variable {B C : Scheme}
  (x : B ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj a)
  (z : B ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj c)
  (y : C ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj b)
  (w : C ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj d)
  [IsOpenImmersion x] [IsOpenImmersion y]
  (hx : x ≫ arithmeticTensorAtlasMap hπ data m j hj a =
    z ≫ arithmeticTensorAtlasMap hπ data m j hj c)
  (hy : y ≫ arithmeticTensorAtlasMap hπ data m j hj b =
    w ≫ arithmeticTensorAtlasMap hπ data m j hj d)


/-- The simultaneous arithmetic transfer is independent of which boundary is changed first. -/
theorem arithmeticDoubleBoundaryTransfer_swap :
    arithmeticDoubleBoundaryTransfer hπ data m j hj a b c d x z y w hx hy ≫
      (pullbackSymmetry (chart c ≫ s) (chart d ≫ s)).hom =
      SchemePairDoubleBoundary.swapSource (chart a ≫ s) (chart b ≫ s) x y ≫
        arithmeticDoubleBoundaryTransfer hπ data m j hj b a d c y w x z hy hx :=
  SchemePairDoubleBoundary.transfer_swap (chart a ≫ s) (chart c ≫ s)
    (chart b ≫ s) (chart d ≫ s) x z y w _ _ (chart a) (chart c) hx (chart b) (chart d) hy

end FLT.Mazur.WeierstrassDividedDepth
