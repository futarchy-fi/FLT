/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor
public import FLT.Mazur.WeierstrassDividedAdjacentInverseAttachment

/-!
# Corrected adjacent tensor boundaries at arbitrary later depths

Use the original multiplicative-scale overlap and the corrected preceding
attachment together. Their full tensor boundaries agree after every retention.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
local notation "d" => data (Fin.mk (j + 1) (by omega))
local notation "e" => data (Fin.mk (j + 2) (by omega))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j) * π)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "v" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "a" => overlapEquiv W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => adjacentBoundaryEquiv hπ d e
local notation "i" => adjacentRetainedOldChart hπ data j hj m hm
local notation "l" => olderSuccessiveChart hπ data (j + 1) hjNext m hm

omit [IsBezout R] in
/-- The corrected original boundary equality keeps the actual multiplicative scale. -/
@[reassoc] theorem adjacentRetainedCorrectedIntegral_boundary :
    Spec.map (CommRingCat.ofHom (AlgEquiv.symm a).toRingHom) ≫
      xOpenInclusion W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) ≫ i =
    Spec.map (CommRingCat.ofHom (AlgEquiv.symm b).toRingHom) ≫
      horizontalOpenInclusion W (π ^ (start + (j + 1))) π
        (Data.b3 e) (Data.b4 e) (Data.b6 e) ≫ l := by
  have hn := congrArg (fun f => (nextBoundaryIso d).inv ≫ f)
    (adjacentRetainedIntegral_boundary hπ data j hj hjNext m hm)
  simp only [nextToX, Category.assoc, Iso.inv_hom_id_assoc] at hn
  have hb := adjacentBoundary_inverse_previousToX hπ d e
  have hl := congrArg (fun f => f ≫ l) hb
  simp only [Category.assoc] at hl
  exact hn.trans hl.symm

local notation "A" => PrincipalOpenTensor.transitionIso S x t a
local notation "B" => PrincipalOpenTensor.transitionIso S x v b

omit [IsBezout R] in
/-- The complete corrected tensor boundary agrees inside every later local model. -/
@[reassoc] theorem adjacentRetainedCorrectedFinite_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫
      adjacentRetainedOldTensorChart hπ data S j hj m hm =
    (B).inv ≫ PrincipalOpenTensor.inclusion S v ≫
      olderSuccessiveTensorChart hπ data (j + 1) hjNext m hm S :=
  TensorOpenChart.common_boundary S x t v a b
    (finiteStructure hπ data (j + 2 + m) hm) i l
    (adjacentRetainedOldChart_structure hπ data j hj m hm)
    (olderSuccessiveChart_structure hπ data (j + 1) hjNext m hm)
    (adjacentRetainedCorrectedIntegral_boundary hπ data j hj hjNext m hm)

/-- Both corrected whole boundaries agree inside every later global model. -/
@[reassoc] theorem adjacentRetainedCorrectedGlobal_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫
      adjacentRetainedOldGlobalTensorChart hπ data S j hj m hm =
    (B).inv ≫ PrincipalOpenTensor.inclusion S v ≫
      olderGlobalTensorChart hπ data S (j + 1) hjNext m hm :=
  adjacentRetainedCorrectedFinite_boundary_assoc hπ data S j hj hjNext m hm
    (finiteLocalTensorEmbedding hπ data S (j + 2 + m) hm)

end FLT.Mazur.WeierstrassDividedDepth
