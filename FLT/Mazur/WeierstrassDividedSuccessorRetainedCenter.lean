/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasRegularCenter
public import FLT.Mazur.WeierstrassDividedSuccessorRetainedCoordinates
public import FLT.Mazur.WeierstrassSuccessiveRegularInputCenter

/-!
# Unit output centers on every actual retained successor input

The entire retained-input branch is refined by all preceding x charts.
Their actual flat projections supply regular centers; the genuine original
addition then forces a unit normalized output center on every member.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "U" => successorRetainedAffineCover hπ data j hj a
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)

/-- Original affine coordinates extracted from each actual retained chart projection. -/
def successorRetainedBeta (i : (U).I₀) : Coordinate W 2 →+* (U).X i :=
  affineChartRingHom (successorRetainedChartProjection hπ data j hj a i ≫
    finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) i.1 ≫
      (E).exteriorChart ≫ finiteToAffine hπ data j (Nat.le_of_succ_le hj))

/-- The extracted coordinates retain the actual original input of the whole successor source. -/
@[reassoc] theorem successorRetainedBeta_original (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom (successorRetainedBeta hπ data j hj a i)) ≫
        integralCurveChart W 2 = successorRetainedOriginalInput hπ data j hj a i := by
  rw [successorRetainedBeta, affineChartRingHom_spec, Category.assoc, Category.assoc,
    Category.assoc, finiteToAffine_toCurve]
  have he := successorRetainedChartProjection_original hπ data j hj a i
  simpa only [finitePrecedingExteriorChart, Category.assoc, finiteLocalChart_contraction] using he

/-- The whole retained atlas supplies regular input generators dividing the later scale. -/
theorem successorRetainedBeta_regularCenter (i : (U).I₀) :
    ∃ x : (U).X i, IsRegular x ∧
      (modificationChartCenter W (π ^ (start + j) * π) 2).map
        (successorRetainedBeta hπ data j hj a i) = Ideal.span {x} ∧
      successorRetainedBeta hπ data j hj a i (algebraMap R _ (π ^ (start + j))) ∈
        Ideal.span {x} := by
  apply finiteExteriorAtlas_regularCenter hπ data j (Nat.le_of_succ_le hj) j le_rfl i.1
    (successorRetainedChartProjection hπ data j hj a i)
  rw [successorRetainedBeta, affineChartRingHom_spec, Category.assoc, Category.assoc,
    Category.assoc, finiteToAffine_toCurve]

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
include ha

/-- Every member of the complete retained-input refinement has unit successive output center. -/
theorem successorRetained_center (i : (U).I₀) :
    (I).map (successorRetainedAlpha hπ data j hj a i) = ⊤ := by
  have hp : successorRetainedParameter hπ data j hj a i ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom (successorRetainedBeta hπ data j hj a i)) ≫
        integralCurveChart W 2) ≫ integralCurveStructure W := by
    rw [successorRetainedBeta_original]
    exact successorRetainedParameter_structure hπ data j hj a i
  obtain ⟨x, hx, hc, hs⟩ := successorRetainedBeta_regularCenter hπ data j hj a i
  apply WeierstrassSuccessiveX.successiveCenter_unit_of_regularInput W (π ^ (start + j)) π
    (e).b3 (e).b4 (e).b6
    (by rw [← factor3_step hπ d e]; exact (d).factor3)
    (by rw [← factor4_step hπ d e]; exact (d).factor4)
    (by rw [← factor6_step hπ d e]; exact (d).factor6)
    (successorRetainedParameter hπ data j hj a i) (successorRetainedAlpha hπ data j hj a i)
    (successorRetainedBeta hπ data j hj a i) hp _ x hx hc hs
  simpa only [successorRetainedBeta_original, previousOriginalMap] using
    successorRetainedAlpha_addition hπ data j hj a ha i

end FLT.Mazur.WeierstrassDividedDepth
