/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderUnequalAddition
public import FLT.Mazur.WeierstrassDividedWiderReflectedNegativeAtlasPair
public import FLT.Mazur.WeierstrassDividedWiderReflectedNegativeCoverage

/-!
# Retained wider reflected addition

Pull the wider reflected output back to full retained pairs without changing
their input depths. Strict numerator depth gives punctured branch coverage.
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
  retainedOlderLowerCoordinates retainedOlderFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m n : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l < j) (hkl : k ≤ l)
  (hdepth : k + 2 * l ≤ m) (hm : m ≤ 2 * (k + l)) (hsum : m - k - l ≤ j) (h2 : W.a₂ = 0)
local notation "hπ" => D.uniformizer_ne_zero

local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, by omega⟩
local notation "e" => data ⟨l, by omega⟩
local notation "hld" => (by change (0 + k) + 2 * (0 + l) ≤ m; omega)
local notation "hmd" => (by change m ≤ 2 * ((0 + k) + (0 + l)); omega)
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => retainedOlderLowerCoordinates hπ data j hj l hl l le_rfl
local notation "hf" => retainedOlderLowerCoordinates_structure hπ data j hj k hk k le_rfl
local notation "hg" => retainedOlderLowerCoordinates_structure hπ data j hj l hl l le_rfl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj a ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj b ≫ t

local notation "input" => olderUnequalFormulaInput hπ data j hj k l hk hl

/-- The constructed wider reflected-depth domain in the full retained older pair. -/
def olderWiderReflectedNegativeOpen : (pullback ta tb).Opens :=
  widerReflectedAtlasPairNegativeOpen D data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change m - (0 + k) - (0 + l) ≤ j; omega) hld hmd h2 f g hf hg

local notation "V" => olderWiderReflectedNegativeOpen D data j hj k l hk hl hkl hdepth hm hsum h2

/-- The retained pair has an actual wider reflected-depth addition into the final smooth model. -/
def olderWiderReflectedNegativeAddition : (V).toScheme ⟶ (U).toScheme :=
  widerReflectedAtlasPairNegativeAddition D data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change m - (0 + k) - (0 + l) ≤ j; omega) hld hmd h2 f g hf hg

/-- The constructed local domain includes into the unchanged full resolved product. -/
def olderWiderReflectedNegativeInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance olderWiderReflectedNegativeInput_open :
    IsOpenImmersion
      (olderWiderReflectedNegativeInput D data j hj k l hk hl hkl hdepth hm hsum h2) := by
  unfold olderWiderReflectedNegativeInput
  infer_instance

/-- Reflected-depth addition preserves the first retained input's coefficient point. -/
@[reassoc] theorem olderWiderReflectedNegativeAddition_structure :
    olderWiderReflectedNegativeAddition D data j hj k l hk hl hkl hdepth hm hsum h2 ≫ t =
      olderWiderReflectedNegativeInput D data j hj k l hk hl hkl hdepth hm hsum h2 ≫
        pullback.fst t t ≫ t := by
  unfold olderWiderReflectedNegativeAddition olderWiderReflectedNegativeInput
  rw [Category.assoc]
  exact widerReflectedAtlasPairNegativeAddition_structure D data j hj a b d e
    (Nat.add_le_add_left hkl 0) (by change m - (0 + k) - (0 + l) ≤ j; omega)
    hld hmd h2 f g hf hg

/-- Reflected-depth addition also preserves the second retained input's coefficient point. -/
@[reassoc] theorem olderWiderReflectedNegativeAddition_structure_snd :
    olderWiderReflectedNegativeAddition D data j hj k l hk hl hkl hdepth hm hsum h2 ≫ t =
      olderWiderReflectedNegativeInput D data j hj k l hk hl hkl hdepth hm hsum h2 ≫
        pullback.snd t t ≫ t := by
  rw [olderWiderReflectedNegativeAddition_structure, pullback.condition]

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "hke" => Nat.add_le_add_left hkl 0
local notation "hdj" => (by change m - (0 + k) - (0 + l) ≤ j; omega)
local notation "T" => UnequalDepthSecantRing hπ d e hke al ar

/-- The retained negative domain maps to its original, unnegated secant source. -/
def olderWiderReflectedNegativeSecantInput : (V).toScheme ⟶ Spec (.of T) :=
  widerReflectedAtlasPairNegativeSecantInput D data j hj a b d e hke hdj hld hmd h2 f g hf hg

/-- The constructed negative sum recovers the original secant after cubic contraction. -/
@[reassoc] theorem olderWiderReflectedNegativeAddition_original :
    olderWiderReflectedNegativeAddition D data j hj k l hk hl hkl hdepth hm hsum h2 ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      olderWiderReflectedNegativeSecantInput D data j hj k l hk hl hkl hdepth hm hsum h2 ≫
        dividedSecantToCurve W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 al
          (unequalDepthRight hπ d e hke ar) (d).factor3 (d).factor4 (d).factor6 := by
  exact widerReflectedAtlasPairNegativeAddition_original D data j hj a b d e hke hdj
    hld hmd h2 f g hf hg

/-- Negative punctured retained inputs are covered in the wider reflected range. -/
theorem olderWiderReflectedNegativeOpen_negative_mem (hk0 : 0 < k) (hlt : k < l)
    (hltm : m < 2 * (k + l))
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : unequalPairLeft d e (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6) ∉
      (input p).asIdeal)
    (hu : unequalPairRight d e (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6) ∉
      (input p).asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6
      (unequalPairLeft d e) ∈
      (input p).asIdeal)
    (hv : dividedTangentBranchFactor W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6
      (unequalPairRight d e) ∈
      (input p).asIdeal) : p ∈ V :=
  widerReflectedNegativeDomain_mem D d e (Nat.add_le_add_left hkl 0)
    data (by change m - (0 + k) - (0 + l) ≤ n; omega)
    hld hmd h2 al ar
    (by change 0 < 0 + k; omega) (by change 0 + k < 0 + l; omega)
    (by change m < 2 * ((0 + k) + (0 + l)); omega) (input p) hp hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
