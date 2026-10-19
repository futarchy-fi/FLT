/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperSplitGenericFiniteness
public import FLT.Mazur.WeierstrassGenericKernelRecovery

/-!
# Finiteness of the original kernel closure over a geometric valuation ring

A finite generic kernel over an algebraically closed fraction field has finitely
many rational points. Properness extends these points to the actual schematic
closure, proving that the whole closure is finite. Nilpotents are retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- Finitely many generic points covering the original kernel prove finiteness of its closure. -/
theorem genericKernelClosureStructure_finite_of_split
    {I : Type} [Finite I] (p : I → (Spec (.of K) ⟶ H))
    (hp : ∀ j, p j ≫ i ≫ integralCurveStructure (W.map (algebraMap R K)) = 𝟙 _)
    (hcover : ∀ x : H, ∃ j : I, x ∈ Set.range (p j)) :
    IsFinite (genericKernelClosureStructure W i) := by
  apply ProperSplitGenericFiniteness.finite_of_split_dense
    (genericKernelClosureStructure W i) (genericKernelToClosure W i)
    (genericKernelToClosure W i).denseRange p _ hcover
  intro j
  rw [genericKernelToClosure_structure, ← Category.assoc,
    hp j, Category.id_comp]

/-- The actual geometric closure of a finite generic kernel is finite over the valuation ring. -/
theorem genericKernelClosureStructure_finite_geometric [IsAlgClosed K]
    [IsFinite (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    IsFinite (genericKernelClosureStructure W i) :=
  ProperSplitGenericFiniteness.finite_of_geometric_dense
    (genericKernelClosureStructure W i) (genericKernelToClosure W i)
    (genericKernelToClosure W i).denseRange
    (i ≫ integralCurveStructure (W.map (algebraMap R K)))
    (genericKernelToClosure_structure W i)

end FLT.Mazur.WeierstrassIntegralChart
