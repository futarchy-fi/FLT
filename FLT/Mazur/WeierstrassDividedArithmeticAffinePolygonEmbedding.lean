/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioInitialEmbedding
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioTensorAffine

/-!
# Complete arithmetic initial affine embeddings

The canonical full affine comparison and its original tensor chart transport
are open immersions at every arithmetic order. All coefficient maps and
quotient squares remain those of the original comparison constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
section Canonical
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  [Fact (IsNilpotent (initialTangentSmoothing W ha s))] (k : ℕ)

/-- The full canonical affine construction embeds with all of its original corrected roots. -/
instance canonicalFactorRatioAffinePolygonMap_isOpenImmersion :
    IsOpenImmersion
      (canonicalFactorRatioAffinePolygonMap W ha s b3 b4 b6 I hI h2 h3 h4 h6 k) := by
  unfold canonicalFactorRatioAffinePolygonMap
  infer_instance
end Canonical

section Arithmetic
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (k : ℕ)

/-- Every arithmetic quotient retains the embedding of the entire actual initial affine chart. -/
instance arithmeticFactorRatioAffinePolygonMap_isOpenImmersion :
    IsOpenImmersion
      (arithmeticFactorRatioAffinePolygonMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k) := by
  unfold arithmeticFactorRatioAffinePolygonMap
  infer_instance
/-- The full corrected initial node retains precisely its original D(q) infinity puncture. -/
theorem arithmeticInitialFactorRatioChart_right_preimage :
    (arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6) ⁻¹'
      Set.range (PolygonSmoothing.rightBranchOpen (Quotient R π m)
        (arithmeticInitialMobiusSmoothing W ha s π m)) =
          Set.range (polynomialNodeOverlapInclusion
            (W.map (algebraMap R (Quotient R π m))) (algebraMap R (Quotient R π m) s)) :=
  polynomialFactorRatioChart_right_preimage ..

end Arithmetic

section Tensor
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (k : ℕ)

/-- The full original tensor affine chart embeds, before or after any quotient reduction. -/
instance arithmeticFactorRatioTensorAffineMap_isOpenImmersion :
    IsOpenImmersion
      (arithmeticFactorRatioTensorAffineMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k) := by
  unfold arithmeticFactorRatioTensorAffineMap
  infer_instance
end Tensor

end FLT.Mazur.WeierstrassDividedDepth
