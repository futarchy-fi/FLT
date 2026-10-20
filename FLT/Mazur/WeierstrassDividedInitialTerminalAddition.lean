/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialFormulaCoordinates
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput
public import FLT.Mazur.WeierstrassDividedAtlasPairIntermediateAddition

/-!
# Initial/terminal formula neighborhoods at every final stage

At common divided depth zero the retained initial chart and final divided
chart have constructed intermediate formula outputs in either order. This
also includes stage zero and the initial self-pair at that stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "hπ" => D.uniformizer_ne_zero
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base

/-- Terminal divided coordinates at common depth zero, including a zero final stage. -/
def terminalZeroFormulaCoordinates :
    globalIntegralAtlasObject data j hj (1 : Fin (j + 3)) ⟶ chart d :=
  depthTransitionMorphism π (0 + 0) (0 + j) hπ (Nat.zero_le _) W
    (d).b3 (d).b4 (d).b6 (e).b3 (e).b4 (e).b6
    (d).factor3 (d).factor4 (d).factor6 (e).factor3 (e).factor4 (e).factor6

omit [IsNoetherianRing R] in
/-- The terminal zero-depth coordinates preserve the original cubic input. -/
@[reassoc] theorem terminalZeroFormulaCoordinates_cubic :
    terminalZeroFormulaCoordinates D data j hj ≫ toCurve d =
      globalIntegralAtlasMap hπ data j hj (1 : Fin (j + 3)) ≫
        finiteGlobalContraction hπ data j hj := by
  change terminalZeroFormulaCoordinates D data j hj ≫ toCurve d =
    finiteSecantDividedChart hπ data j hj ≫ finiteGlobalContraction hπ data j hj
  rw [finiteSecantDividedChart_contraction]
  exact depthTransitionMorphism_contraction π (0 + 0) (0 + j) hπ (Nat.zero_le _) W
    (d).b3 (d).b4 (d).b6 (e).b3 (e).b4 (e).b6
    (d).factor3 (d).factor4 (d).factor6 (e).factor3 (e).factor4 (e).factor6

/-- Select the retained initial chart or the final divided chart in the complete atlas. -/
def initialTerminalFormulaIndex (b : Bool) : Fin (j + 3) :=
  if b then Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ else 1

local notation "idx" => initialTerminalFormulaIndex j

/-- Both whole integral inputs have actual divided coordinates at depth zero. -/
def initialTerminalFormulaCoordinates (b : Bool) :
    globalIntegralAtlasObject data j hj (idx b) ⟶ chart d := by
  cases b
  · exact terminalZeroFormulaCoordinates D data j hj
  · exact retainedInitialFormulaCoordinates data j hj

local notation "f" => initialTerminalFormulaCoordinates D data j hj

omit [IsNoetherianRing R] in
/-- Both selected inputs keep their original cubic contractions. -/
@[reassoc] theorem initialTerminalFormulaCoordinates_cubic (b : Bool) :
    f b ≫ toCurve d =
      globalIntegralAtlasMap hπ data j hj (idx b) ≫ finiteGlobalContraction hπ data j hj := by
  cases b
  · exact terminalZeroFormulaCoordinates_cubic D data j hj
  · exact retainedInitialFormulaCoordinates_cubic hπ data j hj

omit [IsNoetherianRing R] in
/-- The common coordinates preserve the coefficient point required by pair formulas. -/
@[reassoc] theorem initialTerminalFormulaCoordinates_structure (b : Bool) :
    f b ≫ Spec.map (CommRingCat.ofHom (algebraMap R
        (Coordinate W (π ^ 0) (d).b3 (d).b4 (d).b6))) =
      globalIntegralAtlasMap hπ data j hj (idx b) ≫ base := by
  erw [← toCurve_structure d, ← Category.assoc, initialTerminalFormulaCoordinates_cubic,
    Category.assoc]
  rw [finiteGlobalStructure]

local notation "hf" => initialTerminalFormulaCoordinates_structure D data j hj
variable (a b : Bool)
local notation "ta" => globalSmoothAtlasMap hπ data j hj (idx a) ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj (idx b) ≫ t

/-- Formula domain on the genuine full initial/terminal smooth input product. -/
def initialTerminalIntermediateOpen : (pullback ta tb).Opens :=
  atlasPairIntermediateOpen D (by omega) (Nat.zero_le 0) (Nat.zero_le _)
    data (Nat.zero_le n) j hj (idx a) (idx b) d (f a) (f b) (hf a) (hf b)

local notation "V" => initialTerminalIntermediateOpen D data j hj a b

/-- Constructed formula output in the selected final resolved smooth locus. -/
def initialTerminalIntermediateAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairIntermediateAddition D (by omega) (Nat.zero_le 0) (Nat.zero_le _)
    data (Nat.zero_le n) j hj (Nat.zero_le j) (idx a) (idx b) d (f a) (f b) (hf a) (hf b)

local notation "add" => initialTerminalIntermediateAddition D data j hj a b

/-- The constructed output has the coefficient point of the first actual input. -/
@[reassoc] theorem initialTerminalIntermediateAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj (idx a) (idx b) ≫
      pullback.fst t t ≫ t := by
  unfold initialTerminalIntermediateAddition atlasPairIntermediateAddition
  rw [Category.assoc, nodalIntermediatePromotedAddition_structure,
    morphismRestrict_ι_assoc, atlasPairFormulaInput_structure]
  rfl

/-- The second actual input has the same coefficient point as the output. -/
@[reassoc] theorem initialTerminalIntermediateAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj (idx a) (idx b) ≫
      pullback.snd t t ≫ t := by
  rw [initialTerminalIntermediateAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
