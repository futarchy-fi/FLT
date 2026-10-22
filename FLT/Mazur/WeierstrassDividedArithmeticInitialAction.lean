/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasOriginalAction
public import FLT.Mazur.WeierstrassDividedOriginalChartContractions

/-!
# Whole arithmetic retained initial pairs at every finite stage

The unchanged retained initial chart acts on every smooth chart. These outputs retain
the original arithmetic quotient and require no node-depth or stage bound.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  globalTensorAtlasObject arithmeticTensorAtlasMap tensorIntegralAtlasProjection
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (b : Fin (j + 3))
local notation "a" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s

/-- The entire smooth retained initial pair has an actual output over the original quotient. -/
def arithmeticInitialActionQuotientOutput : pullback fa fb ⟶ pullback q t :=
  arithmeticAtlasOriginalActionQuotientOutput hπ data m j hj a b

/-- The complete output retains the original first arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticInitialActionQuotientOutput_base :
    arithmeticInitialActionQuotientOutput hπ data m j hj b ≫ pullback.fst q t =
      pullback.fst fa fb ≫ fa :=
  arithmeticAtlasOriginalActionQuotientOutput_base hπ data m j hj a b

/-- The complete output retains the second arithmetic coefficient morphism too. -/
@[reassoc] theorem arithmeticInitialActionQuotientOutput_base_snd :
    arithmeticInitialActionQuotientOutput hπ data m j hj b ≫ pullback.fst q t =
      pullback.snd fa fb ≫ fb := by
  rw [arithmeticInitialActionQuotientOutput_base, pullback.condition]

/-- The integral projection is the full original action with the second smooth input. -/
@[reassoc] theorem arithmeticInitialActionQuotientOutput_integral :
    arithmeticInitialActionQuotientOutput hπ data m j hj b ≫ pullback.snd q t =
      arithmeticAtlasOriginalActionOutput hπ data m j hj a b :=
  arithmeticAtlasOriginalActionQuotientOutput_integral hπ data m j hj a b

/-- Any smooth chart paired with retained initial in the second position also has a full output. -/
def arithmeticInitialActionReversedOutput : pullback fb fa ⟶ pullback q t :=
  arithmeticAtlasOriginalActionReversedOutput hπ data m j hj a b

/-- Reversing the whole input pair keeps its first arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticInitialActionReversedOutput_base :
    arithmeticInitialActionReversedOutput hπ data m j hj b ≫ pullback.fst q t =
      pullback.fst fb fa ≫ fb :=
  arithmeticAtlasOriginalActionReversedOutput_base hπ data m j hj a b

/-- Swapping the input order back recovers the whole quotient-valued output. -/
@[reassoc] theorem arithmeticInitialActionReversedOutput_swap :
    (pullbackSymmetry fa fb).hom ≫ arithmeticInitialActionReversedOutput hπ data m j hj b =
      arithmeticInitialActionQuotientOutput hπ data m j hj b :=
  arithmeticAtlasOriginalActionReversedOutput_swap hπ data m j hj a b

end FLT.Mazur.WeierstrassDividedDepth
