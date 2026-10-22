/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedDouble
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasTestTransition
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleGluing

/-!
# Whole middle-depth outputs after two terminal transfers

Restrict the actual indexed transfer to the original smooth input pair and
compose with the constructed middle terminal law. No coordinate is discarded.
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


local notation "O₀" => arithmeticLastRetainedPairOpen node data m j hj f
local notation "O" => arithmeticLastRetainedDoubleOpen node data m j hj
local notation "T" => arithmeticLastRetainedDoubleTransfer node data m j hj
local notation "x" => (O).ι ≫ (O₀).ι ≫ pullback.fst f f
local notation "y" => (O).ι ≫ (O₀).ι ≫ pullback.snd f f
local notation "z" => T ≫ pullback.fst g' g'
local notation "w" => T ≫ pullback.snd g' g'
local notation "A" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj
local notation "ft" => (A 1).ι ≫ chart 1 ≫ s
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The original smooth pair open inside the full indexed incidence source. -/
def arithmeticLastRetainedDoubleMiddleSmoothOpen : (O).toScheme.Opens :=
  arithmeticAtlasTestOpen hπ data m (j + 1) hj a a x y

local notation "D" => arithmeticLastRetainedDoubleMiddleSmoothOpen node data m j hj

/-- The full original smooth domain supplies the complete smooth terminal pair. -/
def arithmeticLastRetainedDoubleMiddleSmoothPair : (D).toScheme ⟶ pullback ft ft :=
  arithmeticAtlasTestTarget hπ data m (j + 1) hj a a 1 1 x y z w
    (by simpa only [Category.assoc] using
      (arithmeticLastRetainedDoubleTransfer_first node data m j hj).symm)
    (by simpa only [Category.assoc] using
      (arithmeticLastRetainedDoubleTransfer_second node data m j hj).symm)
    (by simp only [Category.assoc]; rw [pullback.condition])

local notation "pair" => arithmeticLastRetainedDoubleMiddleSmoothPair node data m j hj

/-- Smooth restriction and terminal transfer preserve the complete first resolved input. -/
@[reassoc] theorem arithmeticLastRetainedDoubleMiddleSmoothPair_first :
    pair ≫ pullback.fst ft ft ≫ (A 1).ι ≫ chart 1 =
      (D).ι ≫ (O).ι ≫ (O₀).ι ≫ pullback.fst f f ≫ chart a := by
  rw [arithmeticLastRetainedDoubleMiddleSmoothPair, arithmeticAtlasTestTarget_first]
  rfl

/-- Smooth restriction and terminal transfer preserve the complete second resolved input. -/
@[reassoc] theorem arithmeticLastRetainedDoubleMiddleSmoothPair_second :
    pair ≫ pullback.snd ft ft ≫ (A 1).ι ≫ chart 1 =
      (D).ι ≫ (O).ι ≫ (O₀).ι ≫ pullback.snd f f ≫ chart a := by
  rw [arithmeticLastRetainedDoubleMiddleSmoothPair, arithmeticAtlasTestTarget_second]
  rfl

variable (hm : 2 * (j + 1) = depth)

/-- The whole quotient-valued middle law on the original smooth incidence domain. -/
def arithmeticLastRetainedDoubleMiddleQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pair ≫ arithmeticTerminalSelfMiddleAddition hπ data m (j + 1) hj node (by omega) hm

/-- All nilpotent arithmetic coefficients are retained from the first original input. -/
@[reassoc] theorem arithmeticLastRetainedDoubleMiddleQuotientOutput_base :
    arithmeticLastRetainedDoubleMiddleQuotientOutput node data m j hj hm ≫ pullback.fst q t =
      (D).ι ≫ (O).ι ≫ (O₀).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticLastRetainedDoubleMiddleQuotientOutput, Category.assoc,
    arithmeticTerminalSelfMiddleAddition_base]
  exact arithmeticLastRetainedDoubleMiddleSmoothPair_first_assoc node data m j hj s

/-- The second original input has the same entire arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedDoubleMiddleQuotientOutput_base_snd :
    arithmeticLastRetainedDoubleMiddleQuotientOutput node data m j hj hm ≫ pullback.fst q t =
      (D).ι ≫ (O).ι ≫ (O₀).ι ≫ pullback.snd f f ≫ f := by
  rw [arithmeticLastRetainedDoubleMiddleQuotientOutput_base, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
