/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedSpecialization
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.TensorOpenChartReparametrization

/-!
# The arithmetic retained boundary is the original horizontal transition

The comparison is an equality of full scheme maps in each later finite model.
Both the coefficient projection and every original integral function are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
  (S : Type u) [CommRing S] [Algebra A S]
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "v" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "E" => TensorOpenChart.algebraIso (PrincipalOpenTensor.equiv S x)
local notation "B" => PrincipalOpenTensor.transitionIso S x v (previousBoundaryEquiv hπ d e)
local notation "b" => finiteRetainedBoundaryTensorChart A hπ data j hj m hm S
local notation "g" => olderGlobalTensorChart hπ data S j hj m hm

/-- The whole arithmetic retained tensor open is exactly the original horizontal open. -/
@[reassoc] theorem finiteRetainedBoundaryTensorChart_transition :
    (B).hom ≫ (E).hom ≫ b = PrincipalOpenTensor.inclusion S v ≫ g := by
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteRetainedBoundaryTensorChart_structure,
      TensorOpenChart.algebraIso_structure, PrincipalOpenTensor.transitionIso_structure,
      olderGlobalTensorChart_structure]
    exact (PrincipalOpenTensor.inclusion_structure S v).symm
  · simp only [Category.assoc, olderGlobalTensorChart_integralProjection]
    rw [finiteRetainedBoundaryTensorChart, TensorOpenChart.chart_snd]
    rw [TensorOpenChart.algebraIso_projection_assoc]
    change (B).hom ≫ PrincipalOpenTensor.projection S x ≫ _ = _
    rw [PrincipalOpenTensor.transitionIso_projection_assoc]
    change _ ≫ Spec.map _ ≫ previousToX hπ d e ≫ _ = _
    rw [previousBoundaryEquiv_previousToX_assoc,
      PrincipalOpenTensor.inclusion_projection_assoc]
    rfl

/-- The inverse transition expresses the arithmetic boundary in the full successive chart. -/
@[reassoc] theorem finiteRetainedBoundaryTensorChart_normalized :
    (E).hom ≫ b = (B).inv ≫ PrincipalOpenTensor.inclusion S v ≫ g := by
  apply (cancel_epi (B).hom).mp
  rw [Iso.hom_inv_id_assoc, finiteRetainedBoundaryTensorChart_transition]

end FLT.Mazur.WeierstrassDividedDepth
