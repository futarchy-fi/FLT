/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection
public import FLT.Mazur.WeierstrassDividedFiniteResidueOverlap

/-!
# Full normalized residue intersections

The original middle transition presents the entire fiber product of the
adjacent finite residue charts and their actual global embeddings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "m" => residueMiddleTransition D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

omit [IsBezout R] in
/-- The normalized middle overlap is the full intersection in the finite residue model. -/
theorem finiteResidue_middleOverlap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgEquiv.toRingEquiv m).toRingHom) ≫
      PrincipalOpenTensor.inclusion K x) (PrincipalOpenTensor.inclusion K t)
      (finiteDividedTensorChart hπ data K (j + 1) hj)
      (finiteSuccessiveTensorChart hπ data K j hj) := by
  rw [residueMiddleTransition_eq_integral]
  exact finiteTensor_depthOverlap_isPullback hπ data K j hj

/-- The same normalized maps present the full intersection in the global residue model. -/
theorem globalResidue_middleOverlap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgEquiv.toRingEquiv m).toRingHom) ≫
      PrincipalOpenTensor.inclusion K x) (PrincipalOpenTensor.inclusion K t)
      (globalDividedTensorChart hπ data K (j + 1) hj)
      (globalSuccessiveTensorChart hπ data K j hj) := by
  rw [residueMiddleTransition_eq_integral]
  exact globalTensor_depthOverlap_isPullback hπ data K j hj

end FLT.Mazur.WeierstrassDividedDepth
