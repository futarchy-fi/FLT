/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberSplit
public import FLT.Mazur.SquareZeroReductionSpectrum

/-!
# The original finite node graph has the original source topology

Both the original source projection and the special-fiber reduction induce
homeomorphisms. Their possible square-zero discrepancies are invisible to
this topological statement; no scheme isomorphism is inferred from it.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra

/-- Two kernel functions in the original node reduction multiply to zero. -/
theorem firstNodeReduction_kernel_mul (R : Type) [CommRing R]
    (z w : ChartRing (parameter R 1))
    (hz : firstNodeReduction R z = 0) (hw : firstNodeReduction R w = 0) : z * w = 0 := by
  apply firstNodeBranchPair_injective R
  rw [map_mul, map_zero]
  apply firstNodePairReduction_kernel_mul R
  · rw [firstNodePairReduction_branch, hz, map_zero]
  · rw [firstNodePairReduction_branch, hw, map_zero]

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "s" => completeIdentityFirstGraphSource K n h i
local notation "r" => completeIdentityFirstGraphReduction K n h i
/-- The existing graph ring structure, cached for this construction. -/
local instance completeIdentityFirstGraphTopologyCommRing : CommRing (E) := inferInstance

/-- The unchanged original source of the finite graph induces a homeomorphism on spectra. -/
theorem completeIdentityFirstGraphSource_isHomeomorph :
    IsHomeomorph (PrimeSpectrum.comap (s).toRingHom) := by
  apply SquareZeroReductionKernel.source_comap_isHomeomorph (s).toRingHom (r)
    (firstNodeReduction (R)) (completeIdentityFirstGraphReduction_surjective K n h i)
    (firstNodeReduction_surjective (R))
  · intro z hz
    exact completeIdentityFirstGraphReduction_kernel_mul K n h i z z hz hz
  · intro z hz
    exact firstNodeReduction_kernel_mul (R) z z hz hz
  · apply RingHom.ext
    intro z
    exact completeIdentityFirstGraphReduction_source K n h i z

/-- The original special-fiber reduction also retains exactly the split-node topology. -/
theorem completeIdentityFirstGraphFiberReduction_isHomeomorph :
    IsHomeomorph (PrimeSpectrum.comap (completeIdentityFirstGraphFiberReduction K n h i)) :=
  SquareZeroReductionKernel.comap_isHomeomorph _
    (completeIdentityFirstGraphFiberReduction_surjective K n h i)
    (fun z hz ↦ completeIdentityFirstGraphFiberReduction_kernel_mul K n h i z z hz hz)

end FLT.Mazur.PolygonInfinitesimalStages
