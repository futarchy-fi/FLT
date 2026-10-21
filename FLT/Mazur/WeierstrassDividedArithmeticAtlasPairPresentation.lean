/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairPresentation
public import FLT.Mazur.WeierstrassDividedTensorIntegralAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasIndex

/-!
# Actual arithmetic pairs in the complete smooth integral atlas

At every quotient order, every pair of indexed arithmetic charts supplies
both full smooth integral inputs. The two projections agree with the
original arithmetic charts in the resolved global model.
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
  (m j : ℕ) (hj : j ≤ n)
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "projection" => pullback.fst base q
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj
local notation "atlas" => globalIntegralAtlasMap hπ data j hj
local notation "smooth" => globalSmoothAtlasMap hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base

/-- The exact indexed integral coordinate map retains the original arithmetic chart. -/
@[reassoc] theorem arithmeticAtlasProjection_global (a : Fin (j + 3)) :
    coords a ≫ atlas a = chart a ≫ projection := by
  rw [tensorIntegralAtlasProjection_global, arithmeticTensorAtlasMap, Category.assoc,
    pullbackSymmetry_hom_comp_fst]

/-- Each original arithmetic presentation has its original quotient coefficient map. -/
@[reassoc] theorem arithmeticAtlasProjection_structure (a : Fin (j + 3)) :
    coords a ≫ atlas a ≫ base = (chart a ≫ s) ≫ q := by
  rw [← Category.assoc, arithmeticAtlasProjection_global, Category.assoc,
    pullback.condition]
  rfl

variable [IsNoetherianRing R] (a b : Fin (j + 3))
local notation "A" => tensorIntegralAtlasSmoothOpen hπ data Q j hj a
local notation "B" => tensorIntegralAtlasSmoothOpen hπ data Q j hj b
local notation "fa" => (A).ι ≫ chart a ≫ s
local notation "fb" => (B).ι ≫ chart b ≫ s
local notation "ta" => smooth a ≫ t
local notation "tb" => smooth b ≫ t

/-- Both full smooth arithmetic charts form an actual presentation of the integral atlas pair. -/
def arithmeticAtlasPairPresentation : pullback fa fb ⟶ pullback ta tb :=
  atlasPairPresentation hπ data j hj a b q (chart a ≫ s) (chart b ≫ s)
    (coords a) (coords b) (arithmeticAtlasProjection_structure hπ data m j hj a)
      (arithmeticAtlasProjection_structure hπ data m j hj b)

local notation "input" => arithmeticAtlasPairPresentation hπ data m j hj a b

/-- The first resolved input is precisely the original arithmetic chart's global projection. -/
@[reassoc] theorem arithmeticAtlasPairPresentation_first :
    input ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.fst t t ≫ (base).smoothLocus.ι =
        pullback.fst fa fb ≫ (A).ι ≫ chart a ≫ projection := by
  rw [arithmeticAtlasPairPresentation, atlasPairPresentation_first_global,
    arithmeticAtlasProjection_global]
  rfl

/-- The second resolved input simultaneously retains its original arithmetic projection. -/
@[reassoc] theorem arithmeticAtlasPairPresentation_second :
    input ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.snd t t ≫ (base).smoothLocus.ι =
        pullback.snd fa fb ≫ (B).ι ≫ chart b ≫ projection := by
  rw [arithmeticAtlasPairPresentation, atlasPairPresentation_second_global,
    arithmeticAtlasProjection_global]
  rfl

/-- The integral relative pair has exactly the original common arithmetic coefficient point. -/
@[reassoc] theorem arithmeticAtlasPairPresentation_structure :
    input ≫ pullback.fst ta tb ≫ ta = pullback.fst fa fb ≫ fa ≫ q :=
  atlasPairPresentation_structure hπ data j hj a b q (chart a ≫ s) (chart b ≫ s)
    (coords a) (coords b) (arithmeticAtlasProjection_structure hπ data m j hj a)
      (arithmeticAtlasProjection_structure hπ data m j hj b)

/-- Its second arithmetic coefficient point is the same actual coefficient point. -/
@[reassoc] theorem arithmeticAtlasPairPresentation_structure_snd :
    input ≫ pullback.fst ta tb ≫ ta = pullback.snd fa fb ≫ fb ≫ q := by
  rw [arithmeticAtlasPairPresentation_structure, pullback.condition_assoc]

end FLT.Mazur.WeierstrassDividedDepth
