/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderAtlasFormulaCoordinates
public import FLT.Mazur.WeierstrassDividedAtlasPairIntermediateAddition

/-!
# Actual older/older and mixed older/terminal intermediate additions

Use the retained older chart and final divided chart at their indices in the
complete smooth atlas. Their formula domains carry constructed additions in
both input orders, without assuming an output or divided-input smoothness.
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
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * (0 + k) ≤ m) (hrk : r ≤ 0 + k) (hrm : r ≤ m - 3 * (0 + k))
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hk : k + 1 ≤ n) (s : ℕ) (hs : k + 1 + s ≤ n) (hrj : 0 + k + r ≤ k + 1 + s)
local notation "hπ" => D.uniformizer_ne_zero
local notation "j" => k + 1 + s
local notation "d" => data ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩
local notation "base" => finiteGlobalStructure hπ data j hs
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base

/-- The older chart and terminal chart at their exact complete-atlas indices. -/
def olderTerminalAtlasIndex (b : Bool) : Fin (j + 3) :=
  if b then Fin.succ ⟨s + 1, by clear * - k s; omega⟩ else 1

local notation "idx" => olderTerminalAtlasIndex (k := k) s

/-- Construct common divided coordinates on either entire integral chart. -/
def olderTerminalFormulaCoordinates (b : Bool) :
    globalIntegralAtlasObject data j hs (idx b) ⟶ chart d := by
  cases b
  · exact terminalAtlasFormulaCoordinates hπ data k hk s hs
  · exact olderAtlasFormulaCoordinates hπ data k hk s hs

local notation "f" => olderTerminalFormulaCoordinates D data hk s hs
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R
  (WeierstrassDilatation.Coordinate W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)))

omit [IsNoetherianRing R] in
/-- Both common-coordinate maps preserve the actual coefficient morphism. -/
@[reassoc] theorem olderTerminalFormulaCoordinates_structure (b : Bool) :
    f b ≫ q = globalIntegralAtlasMap hπ data j hs (idx b) ≫ base := by
  cases b
  · exact terminalAtlasFormulaCoordinates_structure hπ data k hk s hs
  · exact olderAtlasFormulaCoordinates_structure hπ data k hk s hs

local notation "hf" => olderTerminalFormulaCoordinates_structure D data hk s hs
variable (a b : Bool)
local notation "ta" => globalSmoothAtlasMap hπ data j hs (idx a) ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hs (idx b) ≫ t

/-- The explicit intermediate formula open for older/older or either mixed chart order. -/
def olderTerminalIntermediateOpen : (pullback ta tb).Opens :=
  atlasPairIntermediateOpen D hdepth hrk hrm data (hrj.trans hs) j hs
    (idx a) (idx b) d (f a) (f b) (hf a) (hf b)

local notation "V" => olderTerminalIntermediateOpen D hdepth hrk hrm data hk s hs hrj a b

/-- Actual addition on the constructed older and mixed chart-pair formula domains. -/
def olderTerminalIntermediateAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairIntermediateAddition D hdepth hrk hrm data (hrj.trans hs) j hs hrj
    (idx a) (idx b) d (f a) (f b) (hf a) (hf b)

local notation "add" => olderTerminalIntermediateAddition D hdepth hrk hrm data hk s hs hrj a b

/-- The older/mixed addition has precisely the coefficient point of the first actual input. -/
@[reassoc] theorem olderTerminalIntermediateAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hs (idx a) (idx b) ≫
      pullback.fst t t ≫ t :=
  atlasPairIntermediateAddition_structure D hdepth hrk hrm data (hrj.trans hs) j hs hrj
    (idx a) (idx b) d (f a) (f b) (hf a) (hf b)

/-- The second actual input has the same original coefficient point. -/
@[reassoc] theorem olderTerminalIntermediateAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hs (idx a) (idx b) ≫
      pullback.snd t t ≫ t := by
  rw [olderTerminalIntermediateAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
