/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTensorIntersection
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts

/-!
# The full adjacent tensor intersection inside the projective model

Embedding the finite model into the global model preserves the exact
principal intersection, including its cartesian scheme structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j + 1 ≤ n)
open WeierstrassSuccessiveX
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "F" => finiteExterior hπ data E₀ (j + 1) hj

local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e)


/-- The actual global tensor inclusions agree on the complete original depth overlap. -/
@[reassoc] theorem globalTensor_depthOverlap :
    (PrincipalOpenTensor.transitionIso S x t a).hom ≫
      PrincipalOpenTensor.inclusion S x ≫ globalDividedTensorChart hπ data S (j + 1) hj =
        PrincipalOpenTensor.inclusion S t ≫ globalSuccessiveTensorChart hπ data S j hj := by
  simp only [globalDividedTensorChart, globalSuccessiveTensorChart, ← Category.assoc]
  exact congrArg (fun f => f ≫ finiteLocalTensorEmbedding hπ data S (j + 1) hj)
    (finiteTensor_depthOverlap hπ data S j hj)

/-- The global chart intersection has no points outside the full tensor principal overlap. -/
theorem globalTensor_depthOverlap_preimage :
    globalSuccessiveTensorChart hπ data S j hj ⁻¹'
      Set.range (globalDividedTensorChart hπ data S (j + 1) hj) =
        Set.range (PrincipalOpenTensor.inclusion S t) := by
  let emb := finiteLocalTensorEmbedding hπ data S (j + 1) hj
  change (emb ∘ finiteSuccessiveTensorChart hπ data S j hj) ⁻¹'
    Set.range (emb ∘ finiteDividedTensorChart hπ data S (j + 1) hj) = _
  rw [Set.range_comp, Set.preimage_comp,
    Set.preimage_image_eq _ emb.isOpenEmbedding.injective]
  exact finiteTensor_depthOverlap_preimage hπ data S j hj

/-- The full principal overlap is the actual cartesian intersection in the global model. -/
theorem globalTensor_depthOverlap_isPullback :
    IsPullback ((PrincipalOpenTensor.transitionIso S x t a).hom ≫
      PrincipalOpenTensor.inclusion S x) (PrincipalOpenTensor.inclusion S t)
      (globalDividedTensorChart hπ data S (j + 1) hj)
      (globalSuccessiveTensorChart hπ data S j hj) := by
  apply IsOpenImmersion.isPullback
  · exact ((Category.assoc _ _ _).trans (globalTensor_depthOverlap hπ data S j hj)).symm
  · exact TopologicalSpace.Opens.ext (globalTensor_depthOverlap_preimage hπ data S j hj)

end FLT.Mazur.WeierstrassDividedDepth
