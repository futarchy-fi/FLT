/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedFiniteResidueOverlap

/-!
# The full normalized overlap glues inside the global model

The original normalized middle transition is the actual global atlas gluing map
after coefficient extension and global embedding, on the full principal opens.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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

/-- The retained middle transition is the full gluing square in the global residue model. -/
@[reassoc] theorem globalResidue_middleOverlap :
    Spec.map (CommRingCat.ofHom (AlgEquiv.toRingEquiv m).toRingHom) ≫
      PrincipalOpenTensor.inclusion K x ≫ globalDividedTensorChart hπ data K (j + 1) hj =
        PrincipalOpenTensor.inclusion K t ≫ globalSuccessiveTensorChart hπ data K j hj := by
  simp only [globalDividedTensorChart, globalSuccessiveTensorChart, ← Category.assoc]
  exact congrArg (fun f => f ≫ finiteLocalTensorEmbedding hπ data K (j + 1) hj)
    (finiteResidue_middleOverlap hπ data D j hj hk0 hk)

end FLT.Mazur.WeierstrassDividedDepth
