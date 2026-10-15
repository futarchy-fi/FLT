/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberPuncture
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberSocle
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphReducedLaw
public import FLT.Mazur.PrincipalOpenSchematicDensityCriterion

/-!
# The precise schematic-density condition for the original first graph

The actual punctured special fiber is schematically dense exactly when
the residual node socle vanishes, or equivalently when the original graph
is flat. Density is a geometric condition still to be proved; the open
isomorphism alone does not supply it.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "Q" => completeIdentityFirstGraphSpecialFiber K n h i
local notation "f" => completeIdentityFirstGraphFiberReduction K n h i
local notation "x" => completeIdentityFirstGraphFiberLeft K n h i
local notation "y" => completeIdentityFirstGraphFiberRight K n h i

/-- Regularity of the unchanged coordinate sum detects reducedness of the literal fiber. -/
theorem completeIdentityFirstGraphFiber_reduced_iff_sum_regular :
    IsReduced (Q) ↔ IsRegular ((x) + (y)) := by
  let _ := splitNodeBranchPair_isReduced (R)
  obtain ⟨m, _, hm⟩ := completeIdentityFirstGraphFiber_kernel_left K n h i
  obtain ⟨j, _, hj⟩ := completeIdentityFirstGraphFiber_kernel_right K n h i
  exact SquareZeroReductionSocle.reduced_iff_sum_regular (f)
    (fun z hz ↦ completeIdentityFirstGraphFiberReduction_kernel_mul K n h i z z hz hz)
    (x) (y) m j hm hj (completeIdentityFirstGraphFiber_reduced_sum_regular K n h i)

/-- Schematic density of the actual puncture is exactly reducedness of the actual fiber. -/
theorem completeIdentityFirstGraphFiber_density_iff_reduced :
    IsSchemeTheoreticallyDominant (PrincipalAffineRefinement.inclusion ((x) + (y))) ↔
      IsReduced (Q) := by
  rw [PrincipalOpenSchematicDensityCriterion.inclusion_iff,
    completeIdentityFirstGraphFiber_reduced_iff_sum_regular]

/-- The node socle is exactly the obstruction to schematic density of the original puncture. -/
theorem completeIdentityFirstGraphFiber_density_iff_socle :
    IsSchemeTheoreticallyDominant (PrincipalAffineRefinement.inclusion ((x) + (y))) ↔
      completeIdentityFirstGraphFiberSocle K n h i = ⊥ := by
  rw [completeIdentityFirstGraphFiber_density_iff_reduced,
    completeIdentityFirstGraphFiber_reduced_iff_socle]

/-- Fiberwise schematic density is equivalent to flatness of the unchanged finite graph. -/
theorem completeIdentityFirstGraphFiber_density_iff_flat :
    IsSchemeTheoreticallyDominant (PrincipalAffineRefinement.inclusion ((x) + (y))) ↔
      Module.Flat (Ring (R) 1) (completeIdentityFirstGraphAlgebra K n h i) := by
  rw [completeIdentityFirstGraphFiber_density_iff_reduced,
    completeIdentityFirstGraphSpecialFiber_reduced_iff_flat]

/-- Proving this literal fiber's density yields the unchanged original first-order law. -/
theorem completeIdentityFiniteLaw_one_of_graphFiber_density
    [IsSchemeTheoreticallyDominant (PrincipalAffineRefinement.inclusion ((x) + (y)))] :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 := by
  let _ := (completeIdentityFirstGraphFiber_density_iff_reduced K n h i).mp inferInstance
  exact completeIdentityFiniteLaw_one_of_graphSpecialFiber_reduced K n h i

end FLT.Mazur.PolygonInfinitesimalStages
