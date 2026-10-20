/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialFormulaCoordinates
public import FLT.Mazur.WeierstrassDividedRetainedOlderCoordinates
public import FLT.Mazur.WeierstrassDividedAtlasPairIntermediateAddition

/-!
# Intermediate formula neighborhoods involving the retained initial chart

Use the actual last initial chart and any retained older chart at a common
zero divided depth. Both input orders and the initial self-pair receive
constructed formula domains and outputs in the selected final smooth locus.
The intermediate output depth is zero; no whole-product coverage is claimed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (l : ℕ) (hl : l < j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base

/-- Select the actual last initial chart or an arbitrary older chart in the same final atlas. -/
def initialOlderFormulaIndex (b : Bool) : Fin (j + 3) :=
  if b then Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩
  else retainedOlderFormulaIndex j l hl

local notation "idx" => initialOlderFormulaIndex j l hl

/-- Common zero-depth coordinates on both entire integral inputs. -/
def initialOlderFormulaCoordinates (b : Bool) :
    globalIntegralAtlasObject data j hj (idx b) ⟶ chart d := by
  cases b
  · exact retainedOlderLowerCoordinates hπ data j hj l hl 0 (Nat.zero_le l)
  · exact retainedInitialFormulaCoordinates data j hj

local notation "f" => initialOlderFormulaCoordinates D data j hj l hl

omit [IsNoetherianRing R] in
/-- Each selected chart keeps its original coefficient point. -/
@[reassoc] theorem initialOlderFormulaCoordinates_structure (b : Bool) :
    f b ≫ Spec.map (CommRingCat.ofHom (algebraMap R
        (WeierstrassDilatation.Coordinate W (π ^ 0) (d).b3 (d).b4 (d).b6))) =
      globalIntegralAtlasMap hπ data j hj (idx b) ≫ base := by
  cases b
  · exact retainedOlderLowerCoordinates_structure hπ data j hj l hl 0 (Nat.zero_le l)
  · exact retainedInitialFormulaCoordinates_structure hπ data j hj

local notation "hf" => initialOlderFormulaCoordinates_structure D data j hj l hl
variable (a b : Bool)
local notation "ta" => globalSmoothAtlasMap hπ data j hj (idx a) ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj (idx b) ≫ t

/-- Actual formula neighborhoods for the initial/older pairs in either input order. -/
def initialOlderIntermediateOpen : (pullback ta tb).Opens :=
  atlasPairIntermediateOpen D (by omega) (Nat.zero_le 0) (Nat.zero_le _)
    data (Nat.zero_le n) j hj (idx a) (idx b) d (f a) (f b) (hf a) (hf b)

local notation "V" => initialOlderIntermediateOpen D data j hj l hl a b

/-- The initial and older inputs have a constructed output on these formula neighborhoods. -/
def initialOlderIntermediateAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairIntermediateAddition D (by omega) (Nat.zero_le 0) (Nat.zero_le _)
    data (Nat.zero_le n) j hj (Nat.zero_le j) (idx a) (idx b) d (f a) (f b) (hf a) (hf b)

local notation "add" => initialOlderIntermediateAddition D data j hj l hl a b

/-- The formula output keeps the base point of the first actual initial or older input. -/
@[reassoc] theorem initialOlderIntermediateAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj (idx a) (idx b) ≫
      pullback.fst t t ≫ t := by
  unfold initialOlderIntermediateAddition atlasPairIntermediateAddition
  rw [Category.assoc, nodalIntermediatePromotedAddition_structure,
    morphismRestrict_ι_assoc, atlasPairFormulaInput_structure]
  rfl

/-- The second actual chart input keeps the same coefficient point as the output. -/
@[reassoc] theorem initialOlderIntermediateAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj (idx a) (idx b) ≫
      pullback.snd t t ≫ t := by
  rw [initialOlderIntermediateAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
