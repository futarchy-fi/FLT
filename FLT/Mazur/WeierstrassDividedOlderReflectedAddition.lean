/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderUnequalAddition
public import FLT.Mazur.WeierstrassDividedReflectedAtlasPair
public import FLT.Mazur.WeierstrassDividedReflectedCoverage

/-!
# Retained reflected-depth addition near terminal inputs

Pull the actual reflected output back to full retained pairs, keeping both
input depths and coefficient points. Positive terminal residual depth gives
coverage even when a reflected-depth output stage is unavailable.
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
  (hdepth : 2 * l ≤ m) (hm : m ≤ k + 2 * l) (hsum : m - k - l ≤ j) (h2 : W.a₂ = 0)
local notation "hπ" => D.uniformizer_ne_zero

local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, by omega⟩
local notation "e" => data ⟨l, by omega⟩
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

/-- The constructed reflected-depth domain in the full retained older pair. -/
def olderReflectedOpen : (pullback ta tb).Opens :=
  atlasPairReflectedOpen D data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change m - (0 + k) - (0 + l) ≤ j; omega)
    (by change 2 * (0 + l) ≤ m; omega)
    (by change m ≤ (0 + k) + 2 * (0 + l); omega) h2 f g hf hg

local notation "V" => olderReflectedOpen D data j hj k l hk hl hkl hdepth hm hsum h2

/-- The retained pair has an actual reflected-depth addition into the final smooth model. -/
def olderReflectedAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairReflectedAddition D data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change m - (0 + k) - (0 + l) ≤ j; omega)
    (by change 2 * (0 + l) ≤ m; omega)
    (by change m ≤ (0 + k) + 2 * (0 + l); omega) h2 f g hf hg

/-- The constructed local domain includes into the unchanged full resolved product. -/
def olderReflectedInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance olderReflectedInput_open :
    IsOpenImmersion (olderReflectedInput D data j hj k l hk hl hkl hdepth hm hsum h2) := by
  unfold olderReflectedInput
  infer_instance

/-- Reflected-depth addition preserves the first retained input's coefficient point. -/
@[reassoc] theorem olderReflectedAddition_structure :
    olderReflectedAddition D data j hj k l hk hl hkl hdepth hm hsum h2 ≫ t =
      olderReflectedInput D data j hj k l hk hl hkl hdepth hm hsum h2 ≫
        pullback.fst t t ≫ t := by
  unfold olderReflectedAddition olderReflectedInput
  rw [Category.assoc]
  exact atlasPairReflectedAddition_structure D data j hj a b d e
    (Nat.add_le_add_left hkl 0) (by change m - (0 + k) - (0 + l) ≤ j; omega)
    (by change 2 * (0 + l) ≤ m; omega)
    (by change m ≤ (0 + k) + 2 * (0 + l); omega) h2 f g hf hg

/-- Reflected-depth addition also preserves the second retained input's coefficient point. -/
@[reassoc] theorem olderReflectedAddition_structure_snd :
    olderReflectedAddition D data j hj k l hk hl hkl hdepth hm hsum h2 ≫ t =
      olderReflectedInput D data j hj k l hk hl hkl hdepth hm hsum h2 ≫
        pullback.snd t t ≫ t := by
  rw [olderReflectedAddition_structure, pullback.condition]

/-- Positive punctured retained inputs are covered near the terminal depth. -/
theorem olderReflectedOpen_positive_mem (hk0 : 0 < k) (hlt : k < l)
    (hltm : 2 * l < m)
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
  reflectedDomain_positive_mem D d e (Nat.add_le_add_left hkl 0)
    data (by change m - (0 + k) - (0 + l) ≤ n; omega)
    (by change 2 * (0 + l) ≤ m; omega)
    (by change m ≤ (0 + k) + 2 * (0 + l); omega)
    h2 (unequalPairLeft d e) (unequalPairRight d e)
    (by change 0 < 0 + k; omega) (by change 0 + k < 0 + l; omega)
    (by change 2 * (0 + l) < m; omega) (input p) hp hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
