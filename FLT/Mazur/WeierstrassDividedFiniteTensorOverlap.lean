/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChartOverlap
public import FLT.Mazur.WeierstrassDividedFiniteOverlap

/-!
# The full tensor overlap inside the finite coefficient extension

The integral depth overlap glues the actual tensor principal opens inside
the finite model, retaining the entire charts rather than one component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j + 1 ≤ n)
open WeierstrassSuccessiveX
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e)

/-- The original depth transition glues the whole tensor overlap inside the finite model. -/
@[reassoc] theorem finiteTensor_depthOverlap :
    (PrincipalOpenTensor.transitionIso S x t a).hom ≫
      PrincipalOpenTensor.inclusion S x ≫ finiteDividedTensorChart hπ data S (j + 1) hj =
        PrincipalOpenTensor.inclusion S t ≫ finiteSuccessiveTensorChart hπ data S j hj :=
  TensorOpenChart.chart_overlap S _ _ _ _ _ x t a (finiteSuccessive_depthOverlap hπ data j hj)

end FLT.Mazur.WeierstrassDividedDepth
