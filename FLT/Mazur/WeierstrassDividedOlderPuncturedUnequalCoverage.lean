/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderNegativeSumDepthAddition
public import FLT.Mazur.WeierstrassDividedPreMiddleBranchDichotomy

/-!
# Coverage of all punctured unequal-depth retained inputs

Positive, negative, and opposite branches exhaust the actual closed-fiber
inputs. Their constructed domains cover every pair with nonzero preceding
abscissae in the sum-depth range, without a supplied branch choice.
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
  (hdepth : 4 * l ≤ m) (hsum : k + l ≤ j) (h2 : W.a₂ = 0)
local notation "hπ" => D.uniformizer_ne_zero

local notation "dd" => olderSumDepthDoubledData D k (by omega)
local notation "ee" => olderSumDepthDoubledData D l hdepth
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, Nat.lt_succ_of_le ((Nat.le_of_lt hk).trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le ((Nat.le_of_lt hl).trans hj)⟩
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

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "α" => algebraMap R (UnequalPairRing d e) W.a₁
local notation "C₁" => dividedTangentBranchFactor W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 al
local notation "C₂" => dividedTangentBranchFactor W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6 ar
local notation "V₊" => olderSumDepthOpen D data j hj k l hk hl hkl hdepth hsum h2
local notation "V₋" => olderNegativeSumDepthOpen D data j hj k l hk hl hkl hdepth hsum h2
local notation "V₀" => olderUnequalOpen hπ data j hj k l hk hl hkl

/-- All branch choices are covered in the full retained pair, assuming only punctured inputs. -/
theorem olderPuncturedUnequal_mem (hk0 : 0 < k) (hlt : k < l)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal) :
    p ∈ V₊ ∨ p ∈ V₋ ∨ p ∈ V₀ := by
  have hkm : 2 * (0 + k) < m := by omega
  have hlm : 2 * (0 + l) < m := by omega
  have hb₁ := preMiddleInput_branch_dichotomy D d al
    (by change 0 < 0 + k; omega) hkm (input p) hp
  have hb₂ := preMiddleInput_branch_dichotomy D e ar
    (by change 0 < 0 + l; omega) hlm (input p) hp
  have h3₁ := preMiddleInput_b3_mem D d hkm (input p) hp
  have h3₂ := preMiddleInput_b3_mem D e hlm (input p) hp
  have neg₁ (h : C₁ ∈ (input p).asIdeal) : y₁ + α * x₁ ∈ (input p).asIdeal := by
    simpa only [dividedTangentBranchFactor, add_sub_cancel_right] using
      (input p).asIdeal.sub_mem h h3₁
  have neg₂ (h : C₂ ∈ (input p).asIdeal) : y₂ + α * x₂ ∈ (input p).asIdeal := by
    simpa only [dividedTangentBranchFactor, add_sub_cancel_right] using
      (input p).asIdeal.sub_mem h h3₂
  rcases hb₁ with hy | hy <;> rcases hb₂ with hv | hv
  · exact Or.inl (olderSumDepthOpen_positive_mem D data j hj k l hk hl hkl hdepth hsum h2
      hk0 hlt p hp hx hu hy hv)
  · exact Or.inr (Or.inr (olderUnequalOpen_opposite_mem hπ data j hj k l hk hl hkl D
      hk0 hlt (by omega) p hp hx hu (Or.inl ⟨hy, neg₂ hv⟩)))
  · exact Or.inr (Or.inr (olderUnequalOpen_opposite_mem hπ data j hj k l hk hl hkl D
      hk0 hlt (by omega) p hp hx hu (Or.inr ⟨neg₁ hy, hv⟩)))
  · exact Or.inr (Or.inl (olderNegativeSumDepthOpen_negative_mem D data j hj k l hk hl hkl
      hdepth hsum h2 hk0 hlt p hp hx hu hy hv))

end FLT.Mazur.WeierstrassDividedDepth
