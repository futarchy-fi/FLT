/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedNodalReversedCover
public import FLT.Mazur.WeierstrassDividedDepthFeasibility

/-!
# Mixed normalized covers at the maximal available stage

The division family forces twice the stage below the node depth. At a
maximal stage, a positive retained depth supplies the remaining near-terminal
bound. Thus the middle and odd endpoints use the same actual three charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedOlderLowerCoordinates retainedOlderFormulaIndex terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k < j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k j hk le_rfl
local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
variable (hk0 : 0 < k) (hmax : depth ≤ 2 * j + 1)
local notation "hd" => dataFamily_twice_stage_le node data j hj
local notation "hn" => (by omega : depth ≤ k + 2 * j)
local notation "H" => arithmeticMixedNodalHorizontalOpen node data m j hj k hk
local notation "J" => arithmeticMixedNodalReversedHorizontalOpen node data m j hj k hk

/-- At the maximal stage the normalized forward cover requires no extra depth premise. -/
def arithmeticMixedNodalMaximalCover : (H).toScheme.OpenCover :=
  arithmeticMixedNodalHorizontalCover node data m j hj k hk hd hn hk0

/-- Every forward chart has its whole quotient-valued output. -/
def arithmeticMixedNodalMaximalOutput (c : Fin 3) :
    (arithmeticMixedNodalMaximalCover node data m j hj k hk hk0 hmax).X c ⟶ pullback q t :=
  arithmeticMixedNodalHorizontalOutput node data m j hj k hk hd hn c

/-- All original arithmetic coefficients survive in the forward maximal-stage output. -/
@[reassoc] theorem arithmeticMixedNodalMaximalOutput_base (c : Fin 3) :
    arithmeticMixedNodalMaximalOutput node data m j hj k hk hk0 hmax c ≫ pullback.fst q t =
      (arithmeticMixedNodalMaximalCover node data m j hj k hk hk0 hmax).f c ≫
        (H).ι ≫ pullback.fst fa fb ≫ fa :=
  arithmeticMixedNodalHorizontalOutput_base node data m j hj k hk hd hn c

/-- The reverse input order has the same automatic bounds and actual normalized cover. -/
def arithmeticMixedNodalMaximalReversedCover : (J).toScheme.OpenCover :=
  arithmeticMixedNodalReversedHorizontalCover node data m j hj k hk hd hn hk0

/-- Every reversed chart retains its complete quotient-valued output. -/
def arithmeticMixedNodalMaximalReversedOutput (c : Fin 3) :
    (arithmeticMixedNodalMaximalReversedCover node data m j hj k hk hk0 hmax).X c ⟶
      pullback q t :=
  arithmeticMixedNodalReversedHorizontalOutput node data m j hj k hk hd hn c

/-- The reversed output retains the original terminal coefficient morphism. -/
@[reassoc] theorem arithmeticMixedNodalMaximalReversedOutput_base (c : Fin 3) :
    arithmeticMixedNodalMaximalReversedOutput node data m j hj k hk hk0 hmax c ≫
      pullback.fst q t =
      (arithmeticMixedNodalMaximalReversedCover node data m j hj k hk hk0 hmax).f c ≫
        (J).ι ≫ pullback.fst fb fa ≫ fb :=
  arithmeticMixedNodalReversedHorizontalOutput_base node data m j hj k hk hd hn c

end FLT.Mazur.WeierstrassDividedDepth
