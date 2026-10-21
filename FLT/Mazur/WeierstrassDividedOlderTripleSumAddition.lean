/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderUnequalAddition
public import FLT.Mazur.WeierstrassDividedAtlasPairQuotientSumAddition
public import FLT.Mazur.WeierstrassDividedTripleSumDepthMiddleCoverage

/-!
# Retained same-branch addition under triple-depth bounds

Construct coefficient quotients from node depth, then pull back the actual
sum-depth output to each full retained pair. This covers additional odd
node depths, with the output stage and middle-depth bounds explicit.
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
  (hdepth : 3 * l ≤ m) (hsum : k + l ≤ j) (h2 : W.a₂ = 0)
local notation "hπ" => D.uniformizer_ne_zero

local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, by omega⟩
local notation "e" => data ⟨l, by omega⟩
local notation "dd" => tripleBranchData D d (by change 3 * (0 + k) ≤ m; omega)
local notation "ee" => tripleBranchData D e (by change 3 * (0 + l) ≤ m; omega)
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
def olderTripleSumDepthOpen : (pullback ta tb).Opens :=
  atlasPairQuotientSumDepthOpen hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + k) + (0 + l) ≤ j; omega) dd ee h2 f g hf hg

local notation "V" => olderTripleSumDepthOpen D data j hj k l hk hl hkl hdepth hsum h2

/-- The retained pair has an actual sum-depth addition into the final smooth model. -/
def olderTripleSumDepthAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairQuotientSumDepthAddition hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + k) + (0 + l) ≤ j; omega) dd ee h2 f g hf hg

/-- The constructed local domain includes into the unchanged full resolved product. -/
def olderTripleSumDepthInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance olderTripleSumDepthInput_open :
    IsOpenImmersion (olderTripleSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2) := by
  unfold olderTripleSumDepthInput
  infer_instance

/-- Sum-depth addition preserves the first retained input's coefficient point. -/
@[reassoc] theorem olderTripleSumDepthAddition_structure :
    olderTripleSumDepthAddition D data j hj k l hk hl hkl hdepth hsum h2 ≫ t =
      olderTripleSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2 ≫
        pullback.fst t t ≫ t := by
  unfold olderTripleSumDepthAddition olderTripleSumDepthInput
  rw [Category.assoc]
  exact atlasPairQuotientSumDepthAddition_structure hπ data j hj a b d e
    (Nat.add_le_add_left hkl 0) (by change (0 + k) + (0 + l) ≤ j; omega)
    dd ee h2 f g hf hg

/-- Sum-depth addition also preserves the second retained input's coefficient point. -/
@[reassoc] theorem olderTripleSumDepthAddition_structure_snd :
    olderTripleSumDepthAddition D data j hj k l hk hl hkl hdepth hsum h2 ≫ t =
      olderTripleSumDepthInput D data j hj k l hk hl hkl hdepth hsum h2 ≫
        pullback.snd t t ≫ t := by
  rw [olderTripleSumDepthAddition_structure, pullback.condition]

/-- Positive punctured retained inputs are covered using triple-depth data. -/
theorem olderTripleSumDepthOpen_positive_mem (hk0 : 0 < k) (hlt : k < l)
    (hm : 2 * (k + l) ≤ m)
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
  tripleSumDepthDomain_le_middle_positive_mem D d e (Nat.add_le_add_left hkl 0)
    data (by change (0 + k) + (0 + l) ≤ n; omega)
    (by change 3 * (0 + l) ≤ m; omega) h2 (unequalPairLeft d e) (unequalPairRight d e)
    (by change 0 < 0 + k; omega) (by change 0 + k < 0 + l; omega)
    (by change 2 * ((0 + k) + (0 + l)) ≤ m; omega) (input p) hp hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
