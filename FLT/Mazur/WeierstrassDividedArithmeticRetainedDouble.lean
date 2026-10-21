/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticDoubleBoundarySmooth

/-!
# Simultaneous boundary changes at arbitrary retained depths

At one common arithmetic stage, advance each retained input by one chart.
The two creation depths are independent and may even be equal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticFixedAdjacentBoundarySource arithmeticFixedAdjacentBoundaryTarget
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "a" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "b" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "x" => arithmeticFixedAdjacentBoundarySource hπ data m k hk i hi
local notation "z" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk i hi
local notation "y" => arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj
local notation "w" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj
local notation "hx" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk i hi
local notation "hy" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk j hj

/-- Both actual incidence conditions in the original retained-depth pair. -/
def arithmeticRetainedDoubleOpen :=
  arithmeticDoubleBoundaryOpen hπ data m k hk a b x y

local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i j hi hj

/-- The first adjacent change followed by the swapped second adjacent change. -/
def arithmeticRetainedDoubleTransfer :=
  arithmeticDoubleBoundaryTransfer hπ data m k hk a b c d x z y w hx hy

local notation "t" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj

/-- The original first input is preserved through both explicit changes. -/
@[reassoc] theorem arithmeticRetainedDoubleTransfer_first :
    t ≫ pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ chart c =
      (D).ι ≫ pullback.fst (chart a ≫ s) (chart b ≫ s) ≫ chart a :=
  arithmeticDoubleBoundaryTransfer_first hπ data m k hk a b c d x z y w hx hy

/-- The original second input is preserved through both explicit changes. -/
@[reassoc] theorem arithmeticRetainedDoubleTransfer_second :
    t ≫ pullback.snd (chart c ≫ s) (chart d ≫ s) ≫ chart d =
      (D).ι ≫ pullback.snd (chart a ≫ s) (chart b ≫ s) ≫ chart b :=
  arithmeticDoubleBoundaryTransfer_second hπ data m k hk a b c d x z y w hx hy

variable [IsNoetherianRing R]

/-- The full simultaneous smooth domain of these original boundary inputs. -/
def arithmeticRetainedDoubleSmoothOpen :=
  arithmeticDoubleBoundarySmoothOpen hπ data m k hk a b x y

local notation "U" => arithmeticRetainedDoubleSmoothOpen hπ data m k hk i j hi hj
local notation "u₁" => (D).ι ≫ pullback.fst (chart a ≫ s) (chart b ≫ s)
local notation "u₂" => (D).ι ≫ pullback.snd (chart a ≫ s) (chart b ≫ s)
local notation "h" => arithmeticDoubleBoundary_source_base hπ data m k hk a b x y

/-- No smooth points are lost by the successive boundary changes. -/
theorem arithmeticRetainedDoubleSmoothOpen_target :
    U = arithmeticAtlasTestOpen hπ data m k hk c d
      (t ≫ pullback.fst (chart c ≫ s) (chart d ≫ s))
      (t ≫ pullback.snd (chart c ≫ s) (chart d ≫ s)) :=
  arithmeticDoubleBoundarySmoothOpen_target hπ data m k hk a b c d x z y w hx hy

/-- Both explicit boundary changes induce the canonical integral atlas-pair transition. -/
def arithmeticRetainedDoubleTransition :
    (U).toScheme ⟶ (atlasPairTransferOpen hπ data k hk a b c d).toScheme :=
  arithmeticDoubleBoundarySmoothTransition hπ data m k hk a b c d x z y w hx hy

/-- The composed integral transition starts from precisely the original arithmetic pair. -/
@[reassoc] theorem arithmeticRetainedDoubleTransition_source :
    arithmeticRetainedDoubleTransition hπ data m k hk i j hi hj ≫
      (atlasPairTransferOpen hπ data k hk a b c d).ι =
      arithmeticAtlasTestPair hπ data m k hk a b u₁ u₂ h ≫
        arithmeticAtlasPairPresentation hπ data m k hk a b :=
  arithmeticDoubleBoundarySmoothTransition_source hπ data m k hk
    a b c d x z y w hx hy


local notation "v₁" => t ≫ pullback.fst (chart c ≫ s) (chart d ≫ s)
local notation "v₂" => t ≫ pullback.snd (chart c ≫ s) (chart d ≫ s)
local notation "h₁" => (arithmeticRetainedDoubleTransfer_first
  hπ data m k hk i j hi hj).symm
local notation "h₂" => (arithmeticRetainedDoubleTransfer_second
  hπ data m k hk i j hi hj).symm

/-- The integral target is precisely the pair after the two adjacent changes. -/
@[reassoc] theorem arithmeticRetainedDoubleTransition_target :
    arithmeticRetainedDoubleTransition hπ data m k hk i j hi hj ≫
      atlasPairTransfer hπ data k hk a b c d =
      arithmeticAtlasTestTarget hπ data m k hk a b c d u₁ u₂ v₁ v₂
        (by simpa only [Category.assoc] using h₁)
        (by simpa only [Category.assoc] using h₂) h ≫
        arithmeticAtlasPairPresentation hπ data m k hk c d :=
  arithmeticDoubleBoundarySmoothTransition_target hπ data m k hk
    a b c d x z y w hx hy

end FLT.Mazur.WeierstrassDividedDepth
