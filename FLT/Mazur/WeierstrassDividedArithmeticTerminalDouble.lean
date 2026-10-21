/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalIndexedBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticDoubleBoundarySmooth

/-!
# Simultaneous terminal changes for both newest inputs

The two original newest-chart inputs independently cross their terminal
boundaries. The exact smooth restriction retains the full integral pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticTerminalIndexedBoundarySource arithmeticTerminalIndexedBoundaryTarget
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "a" => (Fin.succ ⟨j + 1 - j,
  Nat.lt_succ_of_le ((Nat.sub_le (j + 1) j).trans (Nat.le_succ (j + 1)))⟩ : Fin (j + 1 + 3))
local notation "c" => (1 : Fin (j + 1 + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "x" => arithmeticTerminalIndexedBoundarySource hπ data m j hj
local notation "z" => arithmeticTerminalIndexedBoundaryTarget hπ data m j hj
local notation "hx" => arithmeticTerminalIndexedBoundary_ambient hπ data m j hj

/-- Both actual incidence conditions in the original newest-chart pair. -/
def arithmeticTerminalDoubleOpen :=
  arithmeticDoubleBoundaryOpen hπ data m (j + 1) hj a a x x

local notation "D" => arithmeticTerminalDoubleOpen hπ data m j hj

/-- The first terminal change followed by the swapped second terminal change. -/
def arithmeticTerminalDoubleTransfer :=
  arithmeticDoubleBoundaryTransfer hπ data m (j + 1) hj a a c c x z x z hx hx

local notation "t" => arithmeticTerminalDoubleTransfer hπ data m j hj

/-- The original first input is preserved through both explicit changes. -/
@[reassoc] theorem arithmeticTerminalDoubleTransfer_first :
    t ≫ pullback.fst (chart c ≫ s) (chart c ≫ s) ≫ chart c =
      (D).ι ≫ pullback.fst (chart a ≫ s) (chart a ≫ s) ≫ chart a :=
  arithmeticDoubleBoundaryTransfer_first hπ data m (j + 1) hj a a c c x z x z hx hx

/-- The original second input is preserved through both explicit changes. -/
@[reassoc] theorem arithmeticTerminalDoubleTransfer_second :
    t ≫ pullback.snd (chart c ≫ s) (chart c ≫ s) ≫ chart c =
      (D).ι ≫ pullback.snd (chart a ≫ s) (chart a ≫ s) ≫ chart a :=
  arithmeticDoubleBoundaryTransfer_second hπ data m (j + 1) hj a a c c x z x z hx hx

variable [IsNoetherianRing R]

/-- The full simultaneous smooth domain of these original boundary inputs. -/
def arithmeticTerminalDoubleSmoothOpen :=
  arithmeticDoubleBoundarySmoothOpen hπ data m (j + 1) hj a a x x

local notation "U" => arithmeticTerminalDoubleSmoothOpen hπ data m j hj
local notation "u₁" => (D).ι ≫ pullback.fst (chart a ≫ s) (chart a ≫ s)
local notation "u₂" => (D).ι ≫ pullback.snd (chart a ≫ s) (chart a ≫ s)
local notation "h" => arithmeticDoubleBoundary_source_base hπ data m (j + 1) hj a a x x

/-- No smooth points are lost by the successive boundary changes. -/
theorem arithmeticTerminalDoubleSmoothOpen_target :
    U = arithmeticAtlasTestOpen hπ data m (j + 1) hj c c
      (t ≫ pullback.fst (chart c ≫ s) (chart c ≫ s))
      (t ≫ pullback.snd (chart c ≫ s) (chart c ≫ s)) :=
  arithmeticDoubleBoundarySmoothOpen_target hπ data m (j + 1) hj a a c c x z x z hx hx

/-- Both explicit boundary changes induce the canonical integral atlas-pair transition. -/
def arithmeticTerminalDoubleTransition :
    (U).toScheme ⟶ (atlasPairTransferOpen hπ data (j + 1) hj a a c c).toScheme :=
  arithmeticDoubleBoundarySmoothTransition hπ data m (j + 1) hj a a c c x z x z hx hx

/-- The composed integral transition starts from precisely the original arithmetic pair. -/
@[reassoc] theorem arithmeticTerminalDoubleTransition_source :
    arithmeticTerminalDoubleTransition hπ data m j hj ≫
      (atlasPairTransferOpen hπ data (j + 1) hj a a c c).ι =
      arithmeticAtlasTestPair hπ data m (j + 1) hj a a u₁ u₂ h ≫
        arithmeticAtlasPairPresentation hπ data m (j + 1) hj a a :=
  arithmeticDoubleBoundarySmoothTransition_source hπ data m (j + 1) hj
    a a c c x z x z hx hx


local notation "v₁" => t ≫ pullback.fst (chart c ≫ s) (chart c ≫ s)
local notation "v₂" => t ≫ pullback.snd (chart c ≫ s) (chart c ≫ s)
local notation "h₁" => (arithmeticTerminalDoubleTransfer_first
  hπ data m j hj).symm
local notation "h₂" => (arithmeticTerminalDoubleTransfer_second
  hπ data m j hj).symm

/-- The integral target is precisely the pair after the two terminal changes. -/
@[reassoc] theorem arithmeticTerminalDoubleTransition_target :
    arithmeticTerminalDoubleTransition hπ data m j hj ≫
      atlasPairTransfer hπ data (j + 1) hj a a c c =
      arithmeticAtlasTestTarget hπ data m (j + 1) hj a a c c u₁ u₂ v₁ v₂
        (by simpa only [Category.assoc] using h₁)
        (by simpa only [Category.assoc] using h₂) h ≫
        arithmeticAtlasPairPresentation hπ data m (j + 1) hj c c :=
  arithmeticDoubleBoundarySmoothTransition_target hπ data m (j + 1) hj
    a a c c x z x z hx hx

end FLT.Mazur.WeierstrassDividedDepth
