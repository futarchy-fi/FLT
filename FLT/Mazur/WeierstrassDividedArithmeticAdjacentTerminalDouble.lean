/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentIndexedBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalIndexedBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticDoubleBoundarySmooth

/-!
# Simultaneous penultimate adjacent and terminal boundary changes

At stage j+2, change the depth-j input to the next retained chart and the
depth-(j+1) input to the terminal divided chart. This is the actual two-step
boundary transfer on the intersection of both original incidence preimages.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticAdjacentIndexedBoundarySource arithmeticAdjacentIndexedBoundaryTarget
  arithmeticTerminalIndexedBoundarySource arithmeticTerminalIndexedBoundaryTarget
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
local notation "a" => (Fin.succ ⟨j + 2 - j, by omega⟩ : Fin (j + 2 + 3))
local notation "b" => (Fin.succ ⟨j + 1 + 1 - (j + 1), by omega⟩ : Fin (j + 2 + 3))
local notation "c" => (Fin.succ ⟨1, by omega⟩ : Fin (j + 2 + 3))
local notation "d" => (1 : Fin (j + 2 + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 2) hjNext
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 2) hjNext m
local notation "x" => arithmeticAdjacentIndexedBoundarySource hπ data m j hj 0 hjNext
local notation "z" => arithmeticAdjacentIndexedBoundaryTarget hπ data m j hj hjNext 0 hjNext
local notation "y" => arithmeticTerminalIndexedBoundarySource hπ data m (j + 1) hjNext
local notation "w" => arithmeticTerminalIndexedBoundaryTarget hπ data m (j + 1) hjNext
local notation "hx" => arithmeticAdjacentIndexedBoundary_ambient hπ data m j hj hjNext 0 hjNext
local notation "hy" => arithmeticTerminalIndexedBoundary_ambient hπ data m (j + 1) hjNext

/-- Both actual incidence conditions in the original depth-j and depth-(j+1) pair. -/
def arithmeticAdjacentTerminalDoubleOpen :=
  arithmeticDoubleBoundaryOpen hπ data m (j + 2) hjNext a b x y

local notation "D" => arithmeticAdjacentTerminalDoubleOpen hπ data m j hj hjNext

/-- The original adjacent change followed by the swapped original terminal change. -/
def arithmeticAdjacentTerminalDoubleTransfer :=
  arithmeticDoubleBoundaryTransfer hπ data m (j + 2) hjNext a b c d x z y w hx hy

local notation "t" => arithmeticAdjacentTerminalDoubleTransfer hπ data m j hj hjNext

/-- The original first input is preserved through both explicit changes. -/
@[reassoc] theorem arithmeticAdjacentTerminalDoubleTransfer_first :
    t ≫ pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ chart c =
      (D).ι ≫ pullback.fst (chart a ≫ s) (chart b ≫ s) ≫ chart a :=
  arithmeticDoubleBoundaryTransfer_first hπ data m (j + 2) hjNext a b c d x z y w hx hy

/-- The original second input is preserved through both explicit changes. -/
@[reassoc] theorem arithmeticAdjacentTerminalDoubleTransfer_second :
    t ≫ pullback.snd (chart c ≫ s) (chart d ≫ s) ≫ chart d =
      (D).ι ≫ pullback.snd (chart a ≫ s) (chart b ≫ s) ≫ chart b :=
  arithmeticDoubleBoundaryTransfer_second hπ data m (j + 2) hjNext a b c d x z y w hx hy

variable [IsNoetherianRing R]

/-- The full simultaneous smooth domain of these original boundary inputs. -/
def arithmeticAdjacentTerminalDoubleSmoothOpen :=
  arithmeticDoubleBoundarySmoothOpen hπ data m (j + 2) hjNext a b x y

local notation "U" => arithmeticAdjacentTerminalDoubleSmoothOpen hπ data m j hj hjNext
local notation "u₁" => (D).ι ≫ pullback.fst (chart a ≫ s) (chart b ≫ s)
local notation "u₂" => (D).ι ≫ pullback.snd (chart a ≫ s) (chart b ≫ s)
local notation "h" => arithmeticDoubleBoundary_source_base hπ data m (j + 2) hjNext a b x y

/-- No smooth points are lost by the successive boundary changes. -/
theorem arithmeticAdjacentTerminalDoubleSmoothOpen_target :
    U = arithmeticAtlasTestOpen hπ data m (j + 2) hjNext c d
      (t ≫ pullback.fst (chart c ≫ s) (chart d ≫ s))
      (t ≫ pullback.snd (chart c ≫ s) (chart d ≫ s)) :=
  arithmeticDoubleBoundarySmoothOpen_target hπ data m (j + 2) hjNext a b c d x z y w hx hy

/-- Both explicit boundary changes induce the canonical integral atlas-pair transition. -/
def arithmeticAdjacentTerminalDoubleTransition :
    (U).toScheme ⟶ (atlasPairTransferOpen hπ data (j + 2) hjNext a b c d).toScheme :=
  arithmeticDoubleBoundarySmoothTransition hπ data m (j + 2) hjNext a b c d x z y w hx hy

/-- The composed integral transition starts from precisely the original arithmetic pair. -/
@[reassoc] theorem arithmeticAdjacentTerminalDoubleTransition_source :
    arithmeticAdjacentTerminalDoubleTransition hπ data m j hj hjNext ≫
      (atlasPairTransferOpen hπ data (j + 2) hjNext a b c d).ι =
      arithmeticAtlasTestPair hπ data m (j + 2) hjNext a b u₁ u₂ h ≫
        arithmeticAtlasPairPresentation hπ data m (j + 2) hjNext a b :=
  arithmeticDoubleBoundarySmoothTransition_source hπ data m (j + 2) hjNext
    a b c d x z y w hx hy


local notation "v₁" => t ≫ pullback.fst (chart c ≫ s) (chart d ≫ s)
local notation "v₂" => t ≫ pullback.snd (chart c ≫ s) (chart d ≫ s)
local notation "h₁" => (arithmeticAdjacentTerminalDoubleTransfer_first
  hπ data m j hj hjNext).symm
local notation "h₂" => (arithmeticAdjacentTerminalDoubleTransfer_second
  hπ data m j hj hjNext).symm

/-- The integral target is precisely the pair after the adjacent and terminal changes. -/
@[reassoc] theorem arithmeticAdjacentTerminalDoubleTransition_target :
    arithmeticAdjacentTerminalDoubleTransition hπ data m j hj hjNext ≫
      atlasPairTransfer hπ data (j + 2) hjNext a b c d =
      arithmeticAtlasTestTarget hπ data m (j + 2) hjNext a b c d u₁ u₂ v₁ v₂
        (by simpa only [Category.assoc] using h₁)
        (by simpa only [Category.assoc] using h₂) h ≫
        arithmeticAtlasPairPresentation hπ data m (j + 2) hjNext c d :=
  arithmeticDoubleBoundarySmoothTransition_target hπ data m (j + 2) hjNext
    a b c d x z y w hx hy

end FLT.Mazur.WeierstrassDividedDepth
