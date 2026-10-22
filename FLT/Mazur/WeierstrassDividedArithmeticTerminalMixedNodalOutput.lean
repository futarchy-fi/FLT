/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedNodalReversedCover
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalAtlasTransition

/-!
# Normalized outputs after the last retained input transfers to terminal

Use the genuine terminal incidence transfer at the fixed final stage. This
constructs local outputs where the next retained chart does not exist. Both
original inputs survive, including the entire arithmetic coefficient point.
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
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n) (k : ℕ) (hk : k < j + 1)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => (Fin.succ ⟨j + 1 - j, by omega⟩ : Fin (j + 1 + 3))
local notation "b" => retainedOlderFormulaIndex (j + 1) k hk
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj
local notation "fa" => (O 1).ι ≫ chart 1 ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "B" => arithmeticTerminalPairOpen hπ data m j hj (chart b ≫ s)
local notation "x" => arithmeticTerminalAtlasSourceFirst hπ data m j hj b
local notation "y" => arithmeticTerminalAtlasSourceSecond hπ data m j hj b
local notation "z" => arithmeticTerminalAtlasTargetFirst hπ data m j hj b
local notation "w" => arithmeticTerminalAtlasTargetSecond hπ data m j hj b
local notation "h₁" => arithmeticTerminalAtlasInputs_first hπ data m j hj b
local notation "h₂" => congrArg (fun f => f ≫ chart b)
  (arithmeticTerminalAtlasInputs_second hπ data m j hj b)
local notation "hb" => arithmeticTerminalAtlasInputs_base hπ data m j hj b
local notation "D" => arithmeticTerminalAtlasSmoothOpen hπ data m j hj b

/-- The complete smooth terminal-boundary source maps to the actual terminal/retained pair. -/
def arithmeticTerminalMixedNodalTarget : (D).toScheme ⟶ pullback fa fb :=
  arithmeticAtlasTestTarget hπ data m (j + 1) hj a b 1 b x y z w h₁ h₂ hb

local notation "T" => arithmeticTerminalMixedNodalTarget node data m j hj k hk

/-- The transferred terminal input is the entire original newest retained input. -/
@[reassoc] theorem arithmeticTerminalMixedNodalTarget_first :
    T ≫ pullback.fst fa fb ≫ (O 1).ι ≫ chart 1 =
      (D).ι ≫ (B).ι ≫ pullback.fst (old ≫ s) (chart b ≫ s) ≫ old := by
  rw [arithmeticTerminalMixedNodalTarget, arithmeticAtlasTestTarget_first]
  simp only [arithmeticTerminalAtlasSourceFirst, Category.assoc,
    arithmeticBoundaryAtlas_newest]
  rfl

/-- The other retained coordinate stays unchanged as a whole chart-valued morphism. -/
@[reassoc] theorem arithmeticTerminalMixedNodalTarget_second :
    T ≫ pullback.snd fa fb ≫ (O b).ι = (D).ι ≫ y := by
  apply (cancel_mono (chart b)).mp
  simp only [Category.assoc]
  rw [arithmeticTerminalMixedNodalTarget, arithmeticAtlasTestTarget_second]
  rfl

variable (hdepth : 2 * (j + 1) ≤ depth) (hnear : depth ≤ k + 2 * (j + 1))
local notation "E" => arithmeticMixedNodalReversedChart
  node data m (j + 1) hj k hk hdepth hnear

/-- Actual normalized formula domains inside the genuine terminal transfer source. -/
def arithmeticTerminalMixedNodalChart (c : Fin 3) : (D).toScheme.Opens := T ⁻¹ᵁ E c

local notation "C" => arithmeticTerminalMixedNodalChart node data m j hj k hk hdepth hnear

/-- Each terminal-boundary chart has a full quotient-valued output at this same stage. -/
def arithmeticTerminalMixedNodalOutput (c : Fin 3) : (C c).toScheme ⟶ pullback q t :=
  (T ∣_ E c) ≫ arithmeticMixedNodalReversedOutput
    node data m (j + 1) hj k hk hdepth hnear c

/-- The output retains the original newest retained input's full coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalMixedNodalOutput_base (c : Fin 3) :
    arithmeticTerminalMixedNodalOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = (C c).ι ≫ (D).ι ≫ (B).ι ≫
        pullback.fst (old ≫ s) (chart b ≫ s) ≫ old ≫ s := by
  rw [arithmeticTerminalMixedNodalOutput, Category.assoc,
    arithmeticMixedNodalReversedOutput_base, morphismRestrict_ι_assoc]
  rw [arithmeticTerminalMixedNodalTarget_first_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
