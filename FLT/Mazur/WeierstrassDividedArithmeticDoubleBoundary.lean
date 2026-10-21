/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairDoubleBoundaryTransfer
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasTestTransition

/-!
# Both boundary changes in the actual arithmetic atlas

Compose explicit boundary changes in both factors on precisely the two
original boundary preimages. The resulting entire arithmetic pair keeps
both original resolved inputs, including their nilpotent information.
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

/-- The exact simultaneous boundary open of the full original arithmetic pair. -/
def arithmeticDoubleBoundaryOpen : (pullback (chart a ≫ s) (chart b ≫ s)).Opens :=
  SchemePairDoubleBoundary.domain (chart a ≫ s) (chart b ≫ s) x y

local notation "D" => arithmeticDoubleBoundaryOpen hπ data m j hj a b x y

/-- Both original boundary conditions, without an additional output-domain restriction. -/
theorem arithmeticDoubleBoundaryOpen_eq :
    D = pullback.fst (chart a ≫ s) (chart b ≫ s) ⁻¹ᵁ x.opensRange ⊓
      pullback.snd (chart a ≫ s) (chart b ≫ s) ⁻¹ᵁ y.opensRange := rfl

/-- Change the first boundary and then the swapped second boundary on the entire domain. -/
def arithmeticDoubleBoundaryTransfer : (D).toScheme ⟶
    pullback (chart c ≫ s) (chart d ≫ s) :=
  SchemePairDoubleBoundary.transfer (chart a ≫ s) (chart c ≫ s) (chart b ≫ s)
    (chart d ≫ s) x z y w
    (by simpa only [Category.assoc] using congrArg (fun f => f ≫ s) hx)
    (by simpa only [Category.assoc] using congrArg (fun f => f ≫ s) hy)

local notation "t" => arithmeticDoubleBoundaryTransfer hπ data m j hj a b c d x z y w hx hy

/-- The full first arithmetic input is unchanged by both transfers. -/
@[reassoc] theorem arithmeticDoubleBoundaryTransfer_first :
    t ≫ pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ chart c =
      (D).ι ≫ pullback.fst (chart a ≫ s) (chart b ≫ s) ≫ chart a :=
  SchemePairDoubleBoundary.transfer_first_ambient _ _ _ _ x z y w _ _ _ _ hx

/-- The full second arithmetic input is unchanged by both transfers. -/
@[reassoc] theorem arithmeticDoubleBoundaryTransfer_second :
    t ≫ pullback.snd (chart c ≫ s) (chart d ≫ s) ≫ chart d =
      (D).ι ≫ pullback.snd (chart a ≫ s) (chart b ≫ s) ≫ chart b :=
  SchemePairDoubleBoundary.transfer_second_ambient _ _ _ _ x z y w _ _ _ _ hy

/-- The two original inputs retain their common arithmetic coefficient point. -/
theorem arithmeticDoubleBoundary_source_base :
    ((D).ι ≫ pullback.fst (chart a ≫ s) (chart b ≫ s)) ≫ chart a ≫ s =
      ((D).ι ≫ pullback.snd (chart a ≫ s) (chart b ≫ s)) ≫ chart b ≫ s := by
  simp only [Category.assoc, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
