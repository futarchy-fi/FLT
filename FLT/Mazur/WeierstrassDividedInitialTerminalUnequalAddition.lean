/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialFormulaCoordinates
public import FLT.Mazur.WeierstrassDividedTerminalLowerCoordinates
public import FLT.Mazur.WeierstrassDividedAtlasPairUnequalAddition
public import FLT.Mazur.WeierstrassDividedUnequalDepthZeroMiddleCoverage

/-!
# Uncontracted initial/terminal secants at exact middle depth

Keep the initial chart at depth zero and the terminal chart at its full
final depth. The difference-depth output therefore stays at that final
stage. Every closed-fiber pair with punctured initial abscissa is covered
at exact middle depth, without puncturing the terminal input.
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
  retainedInitialFormulaCoordinates terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "a" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "f" => retainedInitialFormulaCoordinates data j hj
local notation "g" => terminalLowerCoordinates hπ data j hj j le_rfl
local notation "hf" => retainedInitialFormulaCoordinates_structure hπ data j hj
local notation "hg" => terminalLowerCoordinates_structure hπ data j hj j le_rfl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj a ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj b ≫ t
local notation "hdepth" => (Nat.zero_le (0 + j))
local notation "hdiff" => (by omega : (0 + j) - (0 + 0) ≤ j)

/-- Both original integral inputs supply their own depths on the full smooth product. -/
def initialTerminalUnequalFormulaInput :
    pullback ta tb ⟶ Spec (.of (UnequalPairRing d e)) :=
  atlasPairUnequalFormulaInput hπ data j hj a b d e f g hf hg

local notation "input" => initialTerminalUnequalFormulaInput hπ data j hj

/-- The initial/terminal formula keeps the exact original coefficient map. -/
@[reassoc] theorem initialTerminalUnequalFormulaInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R (UnequalPairRing d e))) =
      finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.fst t t ≫ t :=
  atlasPairUnequalFormulaInput_structure hπ data j hj a b d e f g hf hg

/-- Actual smooth-output domain in the entire original initial/terminal pair. -/
def initialTerminalUnequalOpen : (pullback ta tb).Opens :=
  atlasPairUnequalOpen hπ data j hj a b d e hdepth hdiff f g hf hg

local notation "V" => initialTerminalUnequalOpen hπ data j hj

/-- The unequal-depth formula gives an output in the unchanged final smooth model. -/
def initialTerminalUnequalAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairUnequalAddition hπ data j hj a b d e hdepth hdiff f g hf hg

/-- The output preserves the first original coefficient point. -/
@[reassoc] theorem initialTerminalUnequalAddition_structure :
    initialTerminalUnequalAddition hπ data j hj ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.fst t t ≫ t :=
  atlasPairUnequalAddition_structure hπ data j hj a b d e hdepth hdiff f g hf hg

/-- The output also preserves the terminal coefficient point. -/
@[reassoc] theorem initialTerminalUnequalAddition_structure_snd :
    initialTerminalUnequalAddition hπ data j hj ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.snd t t ≫ t := by
  rw [initialTerminalUnequalAddition_structure, pullback.condition]

local notation "al" => unequalPairLeft d e
local notation "x₁" => al (x W (π ^ (0 + 0)) (d).b3 (d).b4 (d).b6)

/-- Puncturing only the initial abscissa covers every exact middle-depth terminal input. -/
theorem initialTerminalUnequalOpen_middle_mem [IsLocalRing R] {m : ℕ}
    (D : SplitNodeDepth W π m) (hj0 : 0 < j) (hm : 2 * j = m)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) : p ∈ V :=
  unequalDepthDomain_zero_middle_mem D d e hdepth data ((hdiff).trans hj)
    al (unequalPairRight d e) rfl (by change 0 < 0 + j; omega)
      (by change 2 * (0 + j) = m; omega) (input p) hp hx

end FLT.Mazur.WeierstrassDividedDepth
