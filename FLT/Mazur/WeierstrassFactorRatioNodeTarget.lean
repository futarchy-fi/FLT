/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioInitialOverlap

/-!
# Full factor-ratio maps into a specified adjacent pair of nodes

The polynomial identities apply to any target with the proved standard edge
between its two node maps. This permits independent node smoothing parameters
elsewhere in the target without transporting the original global cover.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
  {Y : Scheme} (c : (b : Bool) → PolygonSmoothing.chart R τ ⟶ Y)
local notation "N" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The actual full node factor ratio, with its original Boolean orientation. -/
def factorRatioNodeTargetMap (b : Bool) : Spec (.of (PolynomialNodeOpen W s)) ⟶ Y :=
  N ≫ (if b then (branchSwapIso R τ).hom else 𝟙 _) ≫ c b

local notation "f" => factorRatioNodeTargetMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 c

instance factorRatioNodeTargetMap_isOpenImmersion
    [∀ b, IsOpenImmersion (c b)] (b : Bool) : IsOpenImmersion (f b) := by
  unfold factorRatioNodeTargetMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

variable (hc : leftBranchOpen R τ ≫ c true = precedingBranch R τ ≫ c false)
include hc

/-- The proved target edge identifies the full reciprocal opposite parameter. -/
@[reassoc] theorem factorRatioNodeTarget_reciprocal :
    (edgeInversion R).hom ≫ rightBranchOpen R τ ≫ (branchSwapIso R τ).hom ≫ c true =
      rightBranchOpen R τ ≫ c false := by
  rw [rightBranchOpen_branchSwapIso_assoc, hc]
  simp only [precedingBranch, ← Category.assoc]
  rw [show (edgeInversion R).hom ≫ (edgeInversion R).hom = 𝟙 _ from
    (edgeInversion R).hom_inv_id, Category.id_comp]

/-- Both complete original node-overlap legs agree in the specified adjacent target pair. -/
@[reassoc] theorem factorRatioNodeTargetMap_overlap :
    polynomialNodeOverlapInclusion W s ≫ f false =
      polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3 ≫ f true := by
  simp only [factorRatioNodeTargetMap, Bool.false_eq_true, ↓reduceIte, Category.id_comp]
  rw [polynomialFactorRatioChart_overlap_first_assoc W ha s τ hτ b3 b4 b6 r hr I hI hrI h3,
    polynomialFactorRatioChart_overlap_opposite_assoc W ha s τ hτ b3 b4 b6 r hr I hI hrI h3,
    factorRatioNodeTarget_reciprocal τ c hc]

end FLT.Mazur.WeierstrassDividedDepth
