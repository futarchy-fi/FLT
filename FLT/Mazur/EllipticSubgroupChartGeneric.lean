/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupChartClosure
public import FLT.Mazur.FinitePointAlgebraInterpolation
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The generic fiber of the concrete elliptic subgroup chart closure

Distinct normalized elliptic points are separated by their coordinates. Finite
interpolation therefore proves that the chart coordinate map is generically
surjective. The affine closure recovers precisely the split algebra of those
subgroup points lying in the chart, with no integrality hypothesis added.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open scoped TensorProduct
open WeierstrassIntegralChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3)

/-- Finite subgroups have only finitely many points in each chart. -/
instance [Finite H] : Finite (Index A W H j) := by
  unfold Index
  infer_instance

/-- Scalar extension of the coordinate map still has the actual coordinate values. -/
theorem genericCoordinateMap_coord (i : Fin 3) (P : Index A W H j) :
    AlgHom.liftEquiv A K (Coordinate W j) (Index A W H j → K)
      (coordinateMap A W H j) (1 ⊗ₜ[A] coord W j i) P = coordinates A W H j P i := by
  change ((1 : K) • coordinateMap A W H j (coord W j i)) P = _
  rw [one_smul, coordinateMap_coord]

/-- The generic chart algebra surjects onto the actual finite point algebra. -/
theorem genericCoordinateMap_surjective [Finite H] :
    Function.Surjective (AlgHom.liftEquiv A K (Coordinate W j) (Index A W H j → K)
      (coordinateMap A W H j)) := by
  refine finitePointAlgebra_surjective (K := K) (B := K ⊗[A] Coordinate W j)
    (ι := Index A W H j)
    (AlgHom.liftEquiv A K (Coordinate W j) (Index A W H j → K)
      (coordinateMap A W H j)) ?_
  intro P Q hPQ
  have hn : coordinates A W H j P ≠ coordinates A W H j Q :=
    fun h => hPQ (coordinates_injective A W H j h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  refine ⟨1 ⊗ₜ[A] coord W j i, ?_⟩
  simpa only [genericCoordinateMap_coord] using hi

/-- The generic fiber of the actual closure equals its prescribed generic chart algebra. -/
def genericEquiv [Finite H] :
    K ⊗[A] Closure A W H j ≃ₐ[K] (Index A W H j → K) :=
  AlgEquiv.ofBijective (AffineGenericClosure.genericMap K (coordinateMap A W H j))
    ⟨AffineGenericClosure.genericMap_injective K (coordinateMap A W H j),
      AffineGenericClosure.genericMap_surjective K (coordinateMap A W H j)
        (genericCoordinateMap_surjective A W H j)⟩

/-- The generic rank counts exactly the subgroup points lying in this chart. -/
theorem generic_finrank [Finite H] :
    Module.finrank K (K ⊗[A] Closure A W H j) = Nat.card (Index A W H j) := by
  classical
  let _ := Fintype.ofFinite (Index A W H j)
  rw [(genericEquiv A W H j).toLinearEquiv.finrank_eq]
  simp only [Module.finrank_pi, Nat.card_eq_fintype_card]

end FLT.Mazur.EllipticSubgroupChart
