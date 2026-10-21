/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticDoubleBoundary

/-!
# Simultaneous arithmetic boundary changes on the exact smooth domain

The composed boundary transfer induces the canonical integral atlas-pair
transition on precisely the simultaneous preimage of both global smooth loci.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
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


local notation "D" => arithmeticDoubleBoundaryOpen hπ data m j hj a b x y
local notation "t" => arithmeticDoubleBoundaryTransfer hπ data m j hj a b c d x z y w hx hy
local notation "u₁" => (D).ι ≫ pullback.fst (chart a ≫ s) (chart b ≫ s)
local notation "u₂" => (D).ι ≫ pullback.snd (chart a ≫ s) (chart b ≫ s)
local notation "v₁" => t ≫ pullback.fst (chart c ≫ s) (chart d ≫ s)
local notation "v₂" => t ≫ pullback.snd (chart c ≫ s) (chart d ≫ s)
local notation "h₁" => (arithmeticDoubleBoundaryTransfer_first
  hπ data m j hj a b c d x z y w hx hy).symm
local notation "h₂" => (arithmeticDoubleBoundaryTransfer_second
  hπ data m j hj a b c d x z y w hx hy).symm
local notation "h" => arithmeticDoubleBoundary_source_base hπ data m j hj a b x y
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "projection" => pullback.fst base
  (Spec.map (CommRingCat.ofHom (algebraMap R Q)))

/-- Both full smooth input preimages on the original simultaneous boundary domain. -/
def arithmeticDoubleBoundarySmoothOpen :=
  arithmeticAtlasTestOpen hπ data m j hj a b u₁ u₂

local notation "U" => arithmeticDoubleBoundarySmoothOpen hπ data m j hj a b x y

/-- Smoothness tests exactly the two original global inputs. -/
theorem arithmeticDoubleBoundarySmoothOpen_eq :
    U = (u₁ ≫ chart a ≫ projection) ⁻¹ᵁ (base).smoothLocus ⊓
      (u₂ ≫ chart b ≫ projection) ⁻¹ᵁ (base).smoothLocus :=
  arithmeticAtlasTestOpen_eq hπ data m j hj a b u₁ u₂

/-- Both boundary changes preserve the complete simultaneous smooth domain. -/
theorem arithmeticDoubleBoundarySmoothOpen_target :
    U = arithmeticAtlasTestOpen hπ data m j hj c d v₁ v₂ :=
  arithmeticAtlasTestTransition_open hπ data m j hj a b c d u₁ u₂ v₁ v₂
    (by simpa only [Category.assoc] using h₁)
    (by simpa only [Category.assoc] using h₂)

/-- The successive explicit changes realize the canonical simultaneous integral transition. -/
def arithmeticDoubleBoundarySmoothTransition :
    (U).toScheme ⟶ (atlasPairTransferOpen hπ data j hj a b c d).toScheme :=
  arithmeticAtlasTestTransition hπ data m j hj a b c d u₁ u₂ v₁ v₂
    (by simpa only [Category.assoc] using h₁)
    (by simpa only [Category.assoc] using h₂) h

/-- The integral source is the original full arithmetic pair presentation. -/
@[reassoc] theorem arithmeticDoubleBoundarySmoothTransition_source :
    arithmeticDoubleBoundarySmoothTransition hπ data m j hj a b c d x z y w hx hy ≫
      (atlasPairTransferOpen hπ data j hj a b c d).ι =
      arithmeticAtlasTestPair hπ data m j hj a b u₁ u₂ h ≫
        arithmeticAtlasPairPresentation hπ data m j hj a b :=
  arithmeticAtlasTestTransition_source hπ data m j hj a b c d u₁ u₂ v₁ v₂ _ _ h

/-- The integral target is exactly the pair obtained by both explicit boundary changes. -/
@[reassoc] theorem arithmeticDoubleBoundarySmoothTransition_target :
    arithmeticDoubleBoundarySmoothTransition hπ data m j hj a b c d x z y w hx hy ≫
      atlasPairTransfer hπ data j hj a b c d =
      arithmeticAtlasTestTarget hπ data m j hj a b c d u₁ u₂ v₁ v₂
        (by simpa only [Category.assoc] using h₁)
        (by simpa only [Category.assoc] using h₂) h ≫
        arithmeticAtlasPairPresentation hπ data m j hj c d :=
  arithmeticAtlasTestTransition_target hπ data m j hj a b c d u₁ u₂ v₁ v₂ _ _ h

end FLT.Mazur.WeierstrassDividedDepth
