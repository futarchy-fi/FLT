/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalLowerCoordinates
public import FLT.Mazur.WeierstrassDividedAtlasPairUnequalAddition

/-!
# Unequal-depth addition on full retained/terminal inputs

The retained factor keeps its own preceding depth. The terminal factor may
keep the final depth or contract to a chosen deeper depth. The difference
output always fits in the final stage, without a sum-depth bound.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l ≤ j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => terminalLowerCoordinates hπ data j hj l hl
local notation "hf" => retainedOlderLowerCoordinates_structure hπ data j hj k hk k le_rfl
local notation "hg" => terminalLowerCoordinates_structure hπ data j hj l hl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj a ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj b ≫ t

/-- The whole mixed pair supplies the two divided coordinates without input smoothness tests. -/
def retainedTerminalUnequalFormulaInput :
    pullback ta tb ⟶ Spec (.of (UnequalPairRing d e)) :=
  atlasPairUnequalFormulaInput hπ data j hj a b d e f g hf hg

local notation "input" => retainedTerminalUnequalFormulaInput hπ data j hj k l hk hl

/-- The retained factor keeps exactly its own preceding-depth contraction. -/
@[reassoc] theorem retainedTerminalUnequalFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) =
      pullback.fst ta tb ≫ (globalSmoothAtlasOpen hπ data j hj a).ι ≫ f :=
  atlasPairUnequalFormulaInput_left hπ data j hj a b d e f g hf hg

/-- The terminal factor retains the selected depth, which may be the final depth itself. -/
@[reassoc] theorem retainedTerminalUnequalFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom) =
      pullback.snd ta tb ≫ (globalSmoothAtlasOpen hπ data j hj b).ι ≫ g :=
  atlasPairUnequalFormulaInput_right hπ data j hj a b d e f g hf hg

variable (hkl : k ≤ l)
local notation "hdepth" => Nat.add_le_add_left hkl 0
local notation "hdiff" => (Nat.sub_le (0 + l) (0 + k)).trans ((Nat.zero_add l).le.trans hl)

/-- The difference-depth output domain on the full retained/terminal product. -/
def retainedTerminalUnequalOpen : (pullback ta tb).Opens :=
  atlasPairUnequalOpen hπ data j hj a b d e hdepth hdiff f g hf hg

local notation "V" => retainedTerminalUnequalOpen hπ data j hj k l hk hl hkl

/-- The output lies in the original final resolved smooth locus. -/
def retainedTerminalUnequalAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairUnequalAddition hπ data j hj a b d e hdepth hdiff f g hf hg

/-- The mixed formula domain embeds openly into the full resolved product. -/
def retainedTerminalUnequalInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance retainedTerminalUnequalInput_open :
    IsOpenImmersion (retainedTerminalUnequalInput hπ data j hj k l hk hl hkl) := by
  unfold retainedTerminalUnequalInput
  infer_instance

/-- The output preserves the first original coefficient point. -/
@[reassoc] theorem retainedTerminalUnequalAddition_structure :
    retainedTerminalUnequalAddition hπ data j hj k l hk hl hkl ≫ t =
      retainedTerminalUnequalInput hπ data j hj k l hk hl hkl ≫ pullback.fst t t ≫ t := by
  unfold retainedTerminalUnequalAddition retainedTerminalUnequalInput
  rw [Category.assoc]
  exact atlasPairUnequalAddition_structure hπ data j hj a b d e hdepth hdiff f g hf hg

/-- The output also preserves the original terminal factor's coefficient point. -/
@[reassoc] theorem retainedTerminalUnequalAddition_structure_snd :
    retainedTerminalUnequalAddition hπ data j hj k l hk hl hkl ≫ t =
      retainedTerminalUnequalInput hπ data j hj k l hk hl hkl ≫ pullback.snd t t ≫ t := by
  rw [retainedTerminalUnequalAddition_structure, pullback.condition]

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "α" => algebraMap R (UnequalPairRing d e) W.a₁

/-- Opposite punctured mixed inputs are covered even when their depth sum exceeds the stage. -/
theorem retainedTerminalUnequalOpen_opposite_mem [IsLocalRing R] {m : ℕ}
    (D : SplitNodeDepth W π m) (hk0 : 0 < k) (hlt : k < l) (hm : 2 * l < m)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hb : (y₁ ∈ (input p).asIdeal ∧ y₂ + α * x₂ ∈ (input p).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input p).asIdeal ∧ y₂ ∈ (input p).asIdeal)) : p ∈ V :=
  atlasPairUnequalOpen_opposite_mem hπ data j hj a b d e hdepth hdiff f g hf hg D
    (by change 0 < 0 + k; omega) (by change 0 + k < 0 + l; omega)
    (by change 2 * (0 + l) < m; omega) p hp hx hu hb

end FLT.Mazur.WeierstrassDividedDepth
