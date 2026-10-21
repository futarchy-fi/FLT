/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderCommonSumAddition
public import FLT.Mazur.WeierstrassDividedCommonNegativeAtlasPair
public import FLT.Mazur.WeierstrassDividedCommonNegativeCoverage

/-!
# Negative mixed-depth addition on retained older charts

Construct the input coefficient quotients from node depth, then pull back the actual
sum-depth output to each exact retained pair. The complete pair cover is
unchanged; negative punctured inputs in the stated depth range are covered.
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
  (hdepth : k + 2 * l ≤ m) (hsum : k + l ≤ j) (h2 : W.a₂ = 0)
local notation "hπ" => D.uniformizer_ne_zero

local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, by omega⟩
local notation "e" => data ⟨l, by omega⟩
local notation "dd" => tripleBranchData D d (by change 3 * (0 + k) ≤ m; omega)
local notation "ee" => commonBranchData D e (by change (0 + k) + 2 * (0 + l) ≤ m; omega)
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

/-- The constructed sum-depth domain in the full retained older pair. -/
def olderCommonNegativeSumDepthOpen : (pullback ta tb).Opens :=
  commonAtlasPairNegativeSumDepthOpen hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + k) + (0 + l) ≤ j; omega) dd ee h2 f g hf hg

local notation "V" => olderCommonNegativeSumDepthOpen D data j hj k l hk hl hkl hdepth hsum h2

/-- The retained pair has an actual sum-depth addition into the final smooth model. -/
def olderCommonNegativeSumDepthAddition : (V).toScheme ⟶ (U).toScheme :=
  commonAtlasPairNegativeSumDepthAddition hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + k) + (0 + l) ≤ j; omega) dd ee h2 f g hf hg

/-- The constructed local domain includes into the unchanged full resolved product. -/
def olderCommonNegativeSumDepthInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance olderCommonNegativeSumDepthInput_open :
    IsOpenImmersion
      (olderCommonNegativeSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2) := by
  unfold olderCommonNegativeSumDepthInput
  infer_instance

/-- Sum-depth addition preserves the first retained input's coefficient point. -/
@[reassoc] theorem olderCommonNegativeSumDepthAddition_structure :
    olderCommonNegativeSumDepthAddition D data j hj k l hk hl hkl hdepth hsum h2 ≫ t =
      olderCommonNegativeSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2 ≫
        pullback.fst t t ≫ t := by
  unfold olderCommonNegativeSumDepthAddition olderCommonNegativeSumDepthInput
  rw [Category.assoc]
  exact commonAtlasPairNegativeSumDepthAddition_structure hπ data j hj a b d e
    (Nat.add_le_add_left hkl 0) (by change (0 + k) + (0 + l) ≤ j; omega)
    dd ee h2 f g hf hg

/-- Sum-depth addition also preserves the second retained input's coefficient point. -/
@[reassoc] theorem olderCommonNegativeSumDepthAddition_structure_snd :
    olderCommonNegativeSumDepthAddition D data j hj k l hk hl hkl hdepth hsum h2 ≫ t =
      olderCommonNegativeSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2 ≫
        pullback.snd t t ≫ t := by
  rw [olderCommonNegativeSumDepthAddition_structure, pullback.condition]

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "hke" => Nat.add_le_add_left hkl 0
local notation "hdj" => (by change (0 + k) + (0 + l) ≤ j; omega)
local notation "T" => UnequalDepthSecantRing hπ d e hke al ar

/-- The retained negative domain maps to its original, unnegated secant source. -/
def olderCommonNegativeSumDepthSecantInput : (V).toScheme ⟶ Spec (.of T) :=
  commonAtlasPairNegativeSumDepthSecantInput hπ data j hj a b d e hke hdj dd ee h2 f g hf hg

/-- The constructed negative sum recovers the original secant after cubic contraction. -/
@[reassoc] theorem olderCommonNegativeSumDepthAddition_original :
    olderCommonNegativeSumDepthAddition D data j hj k l hk hl hkl hdepth hsum h2 ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      olderCommonNegativeSumDepthSecantInput D data j hj k l hk hl hkl hdepth hsum h2 ≫
        dividedSecantToCurve W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 al
          (unequalDepthRight hπ d e hke ar) (d).factor3 (d).factor4 (d).factor6 := by
  exact commonAtlasPairNegativeSumDepthAddition_original hπ data j hj a b d e hke hdj
    dd ee h2 f g hf hg

/-- Negative punctured retained inputs are covered using mixed-depth data. -/
theorem olderCommonNegativeSumDepthOpen_negative_mem (hk0 : 0 < k) (hlt : k < l)
    (hm : 2 * (k + l) ≤ m)
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
  commonNegativeSumDepthDomain_mem D d e (Nat.add_le_add_left hkl 0)
    data (by change (0 + k) + (0 + l) ≤ n; omega)
    (by change (0 + k) + 2 * (0 + l) ≤ m; omega) h2 al ar
    (by change 0 < 0 + k; omega) (by change 0 + k < 0 + l; omega)
    (by change 2 * ((0 + k) + (0 + l)) ≤ m; omega) (input p) hp hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
