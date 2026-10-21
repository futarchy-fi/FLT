/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedTerminalUnequalAddition
public import FLT.Mazur.WeierstrassDividedOlderSumDepthAddition
public import FLT.Mazur.WeierstrassDividedAtlasPairSumDepthAddition
public import FLT.Mazur.WeierstrassNodalDividedDepth

/-!
# Same-branch sum-depth addition on retained/terminal charts

Construct the doubled input data from node depth, then pull back the actual
sum-depth output to each exact retained/terminal pair. The complete pair
cover is unchanged; positive punctured inputs in the stated depth range are covered.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedOlderLowerCoordinates retainedOlderFormulaIndex terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m n : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l ≤ j) (hkl : k ≤ l)
  (hdepth : 4 * l ≤ m) (hsum : k + l ≤ j) (h2 : W.a₂ = 0)
local notation "hπ" => D.uniformizer_ne_zero

local notation "dd" => olderSumDepthDoubledData D k (by omega)
local notation "ee" => olderSumDepthDoubledData D l hdepth
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, by omega⟩
local notation "e" => data ⟨l, by omega⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => terminalLowerCoordinates hπ data j hj l hl
local notation "hf" => retainedOlderLowerCoordinates_structure hπ data j hj k hk k le_rfl
local notation "hg" => terminalLowerCoordinates_structure hπ data j hj l hl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj a ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj b ≫ t

local notation "input" => retainedTerminalUnequalFormulaInput hπ data j hj k l hk hl

/-- The constructed sum-depth domain in the full retained/terminal pair. -/
def retainedTerminalSumDepthOpen : (pullback ta tb).Opens :=
  atlasPairSumDepthOpen hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + k) + (0 + l) ≤ j; omega) dd ee h2 f g hf hg

local notation "V" => retainedTerminalSumDepthOpen D data j hj k l hk hl hkl hdepth hsum h2

/-- The retained/terminal pair has an actual sum-depth addition into the final smooth model. -/
def retainedTerminalSumDepthAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairSumDepthAddition hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + k) + (0 + l) ≤ j; omega) dd ee h2 f g hf hg

/-- The constructed local domain includes into the unchanged full resolved product. -/
def retainedTerminalSumDepthInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance retainedTerminalSumDepthInput_open :
    IsOpenImmersion (retainedTerminalSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2) := by
  unfold retainedTerminalSumDepthInput
  infer_instance

/-- Sum-depth addition preserves the first retained input's coefficient point. -/
@[reassoc] theorem retainedTerminalSumDepthAddition_structure :
    retainedTerminalSumDepthAddition D data j hj k l hk hl hkl hdepth hsum h2 ≫ t =
      retainedTerminalSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2 ≫
        pullback.fst t t ≫ t := by
  unfold retainedTerminalSumDepthAddition retainedTerminalSumDepthInput
  rw [Category.assoc]
  exact atlasPairSumDepthAddition_structure hπ data j hj a b d e
    (Nat.add_le_add_left hkl 0) (by change (0 + k) + (0 + l) ≤ j; omega)
    dd ee h2 f g hf hg

/-- Sum-depth addition also preserves the second retained input's coefficient point. -/
@[reassoc] theorem retainedTerminalSumDepthAddition_structure_snd :
    retainedTerminalSumDepthAddition D data j hj k l hk hl hkl hdepth hsum h2 ≫ t =
      retainedTerminalSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2 ≫
        pullback.snd t t ≫ t := by
  rw [retainedTerminalSumDepthAddition_structure, pullback.condition]

/-- Positive punctured mixed inputs are covered using doubled data from node depth. -/
theorem retainedTerminalSumDepthOpen_positive_mem (hk0 : 0 < k) (hlt : k < l)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : unequalPairLeft d e (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6) ∉
      (input p).asIdeal)
    (hu : unequalPairRight d e (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6) ∉
      (input p).asIdeal)
    (hy : unequalPairLeft d e (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6) ∈
      (input p).asIdeal)
    (hv : unequalPairRight d e (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6) ∈
      (input p).asIdeal) : p ∈ V :=
  atlasPairSumDepthOpen_positive_mem hπ data j hj a b d e
    (Nat.add_le_add_left hkl 0) (by change (0 + k) + (0 + l) ≤ j; omega)
    dd ee h2 f g hf hg D (by change 0 < 0 + k; omega)
    (by change 0 + k < 0 + l; omega)
    (by change 2 * ((0 + k) + (0 + l)) < m; omega) p hp hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
