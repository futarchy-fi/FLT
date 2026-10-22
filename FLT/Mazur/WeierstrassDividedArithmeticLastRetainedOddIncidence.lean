/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMiddleOutput
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfOddCover

/-!
# Odd terminal outputs on the last retained incidence source

The existing full smooth incidence transfer has no middle-depth hypothesis.
Pull back the two genuine odd-terminal self formulas along it, preserving
both original inputs and the entire arithmetic coefficient morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g'" => chart 1 ≫ s
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj


local notation "O" => arithmeticLastRetainedPairOpen node data m j hj g'
local notation "T" => arithmeticLastRetainedPairTransfer node data m j hj g'
local notation "x" => (O).ι ≫ pullback.fst f g'
local notation "y" => (O).ι ≫ pullback.snd f g'
local notation "z" => T ≫ pullback.fst g' g'
local notation "w" => T ≫ pullback.snd g' g'
local notation "A" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj
local notation "ft" => (A 1).ι ≫ chart 1 ≫ s
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "D" => arithmeticLastRetainedMiddleSmoothOpen node data m j hj
local notation "pair" => arithmeticLastRetainedMiddleSmoothPair node data m j hj
variable (hodd : depth = 2 * (j + 1) + 1)
local notation "E" => arithmeticTerminalSelfOddChart node data m (j + 1) hj (by omega) hodd

/-- Both genuine terminal self domains pull back to the original smooth incidence source. -/
def arithmeticLastRetainedOddIncidenceChart (flag : Bool) : (D).toScheme.Opens :=
  pair ⁻¹ᵁ E flag

local notation "C" => arithmeticLastRetainedOddIncidenceChart node data m j hj hodd

/-- Each incidence chart carries its entire odd-terminal quotient output. -/
def arithmeticLastRetainedOddIncidenceOutput (flag : Bool) :
    (C flag).toScheme ⟶ pullback q t :=
  (pair ∣_ E flag) ≫ arithmeticTerminalSelfOddChartOutput
    node data m (j + 1) hj (by omega) hodd flag

/-- The complete coefficient morphism of the original retained input survives. -/
@[reassoc] theorem arithmeticLastRetainedOddIncidenceOutput_base (flag : Bool) :
    arithmeticLastRetainedOddIncidenceOutput node data m j hj hodd flag ≫ pullback.fst q t =
      (C flag).ι ≫ (D).ι ≫ (O).ι ≫ pullback.fst f g' ≫ f := by
  rw [arithmeticLastRetainedOddIncidenceOutput, Category.assoc,
    arithmeticTerminalSelfOddChartOutput_base, morphismRestrict_ι_assoc]
  change (C flag).ι ≫ pair ≫ pullback.fst ft ft ≫ (A 1).ι ≫ chart 1 ≫ s = _
  rw [arithmeticLastRetainedMiddleSmoothPair_first_assoc]

/-- The two genuine output charts cover the full original smooth incidence domain. -/
theorem arithmeticLastRetainedOddIncidenceChart_covers : (⨆ flag, C flag) = ⊤ := by
  apply top_unique
  intro p _
  rcases arithmeticTerminalSelfOdd_or_reciprocal_mem
    node data m (j + 1) hj (by omega) hodd (pair p) with hp | hp
  · exact (le_iSup (fun flag => C flag) false) hp
  · exact (le_iSup (fun flag => C flag) true) hp

/-- A full smooth incidence cover with no original horizontal puncture. -/
def arithmeticLastRetainedOddIncidenceCover : (D).toScheme.OpenCover :=
  (D).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedOddIncidenceChart_covers node data m j hj hodd)

end FLT.Mazur.WeierstrassDividedDepth
