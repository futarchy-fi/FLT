/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderUnequalAddition
public import FLT.Mazur.WeierstrassDividedNodalWiderReflectedNegativeAtlasPair
public import FLT.Mazur.WeierstrassDividedNodalWiderReflectedNegative

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
  (hdepth : k + 2 * l ≤ m) (hm : m ≤ 2 * (k + l)) (hsum : m - k - l ≤ j)
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
def olderNodalWiderReflectedNegativeOpen : (pullback ta tb).Opens :=
  nodalWiderReflectedAtlasPairNegativeOpen D data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change m - (0 + k) - (0 + l) ≤ j; omega) hld hmd f g hf hg

local notation "V" => olderNodalWiderReflectedNegativeOpen D data j hj k l hk hl hkl hdepth hm hsum

/-- The retained pair has an actual wider reflected-depth addition into the final smooth model. -/
def olderNodalWiderReflectedNegativeAddition : (V).toScheme ⟶ (U).toScheme :=
  nodalWiderReflectedAtlasPairNegativeAddition D data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change m - (0 + k) - (0 + l) ≤ j; omega) hld hmd f g hf hg

/-- The constructed local domain includes into the unchanged full resolved product. -/
def olderNodalWiderReflectedNegativeInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance olderNodalWiderReflectedNegativeInput_open :
    IsOpenImmersion
      (olderNodalWiderReflectedNegativeInput D data j hj k l hk hl hkl hdepth hm hsum) := by
  unfold olderNodalWiderReflectedNegativeInput
  infer_instance

/-- Reflected-depth addition preserves the first retained input's coefficient point. -/
@[reassoc] theorem olderNodalWiderReflectedNegativeAddition_structure :
    olderNodalWiderReflectedNegativeAddition D data j hj k l hk hl hkl hdepth hm hsum ≫ t =
      olderNodalWiderReflectedNegativeInput D data j hj k l hk hl hkl hdepth hm hsum ≫
        pullback.fst t t ≫ t := by
  unfold olderNodalWiderReflectedNegativeAddition olderNodalWiderReflectedNegativeInput
  rw [Category.assoc]
  exact nodalWiderReflectedAtlasPairNegativeAddition_structure D data j hj a b d e
    (Nat.add_le_add_left hkl 0) (by change m - (0 + k) - (0 + l) ≤ j; omega)
    hld hmd f g hf hg

/-- Reflected-depth addition also preserves the second retained input's coefficient point. -/
@[reassoc] theorem olderNodalWiderReflectedNegativeAddition_structure_snd :
    olderNodalWiderReflectedNegativeAddition D data j hj k l hk hl hkl hdepth hm hsum ≫ t =
      olderNodalWiderReflectedNegativeInput D data j hj k l hk hl hkl hdepth hm hsum ≫
        pullback.snd t t ≫ t := by
  rw [olderNodalWiderReflectedNegativeAddition_structure, pullback.condition]

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "hke" => Nat.add_le_add_left hkl 0
local notation "hdj" => (by change m - (0 + k) - (0 + l) ≤ j; omega)
local notation "T" => UnequalDepthSecantRing hπ d e hke al ar

/-- Negative punctured retained inputs are covered in the wider reflected range. -/
theorem olderNodalWiderReflectedNegativeOpen_negative_mem (hk0 : 0 < k) (hlt : k < l)
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
  nodalWiderReflectedNegativeDomain_mem D d e (Nat.add_le_add_left hkl 0)
    data (by change m - (0 + k) - (0 + l) ≤ n; omega)
    hld hmd al ar
    (by change 0 < 0 + k; omega) (by change 0 + k < 0 + l; omega)
    (by change m < 2 * ((0 + k) + (0 + l)); omega) (input p) hp hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
