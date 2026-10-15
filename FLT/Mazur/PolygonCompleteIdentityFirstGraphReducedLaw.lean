/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphSpecialFiber
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFlat

/-!
# Reduced special fiber detects the unchanged original first-order law

The literal special fiber of the constructed graph is reduced exactly when
the graph is flat over the original coefficient ring. Either condition
therefore gives the unchanged law. Reducedness is a remaining geometric
assertion, not an instance provided by this construction.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "C" => firstNodeBranchSubalgebra (R)
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "G" => completeIdentityFirstGraphAlgebra K n h i
local notation "s" => completeIdentityFirstGraphSource K n h i
/-- The existing graph ring structure, cached for this construction. -/
local instance completeIdentityFirstGraphReducedLawCommRing : CommRing (E) := inferInstance

/-- Surjectivity of the actual finite source is equality with the original node subalgebra. -/
theorem completeIdentityFirstGraphSource_surjective_iff :
    Function.Surjective (s) ↔ (G) = (C) := by
  constructor
  · intro hs
    apply le_antisymm
    · intro z hz
      have he : z ∈ (E) := by
        change z ∈ (E).restrictScalars (S)
        rw [completeIdentityFirstErrorAlgebra_eq_graph]
        exact hz
      obtain ⟨w, hw⟩ := hs ⟨z, he⟩
      exact ⟨w, congrArg Subtype.val hw⟩
    · exact le_sup_left
  · intro he z
    have hz : z.val ∈ (G) := by
      rw [← completeIdentityFirstErrorAlgebra_eq_graph]
      exact z.property
    rw [he] at hz
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, Subtype.ext hw⟩

/-- Reducedness of the actual graph special fiber is exactly coefficient-base flatness. -/
theorem completeIdentityFirstGraphSpecialFiber_reduced_iff_flat :
    IsReduced (completeIdentityFirstGraphSpecialFiber K n h i) ↔ Module.Flat (S) (G) := by
  rw [completeIdentityFirstGraphSpecialFiber_reduced_iff,
    completeIdentityFirstGraphSource_surjective_iff,
    completeIdentityFirstGraphAlgebra_eq_source_iff, completeIdentityFirstGraphFlat_iff_preserves]

/-- A reduced actual special fiber supplies the original, unchanged first positive-order law. -/
theorem completeIdentityFiniteLaw_one_of_graphSpecialFiber_reduced
    [IsReduced (completeIdentityFirstGraphSpecialFiber K n h i)] :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 := by
  let _ := (completeIdentityFirstGraphSpecialFiber_reduced_iff_flat K n h i).mp inferInstance
  exact completeIdentityFiniteLaw_one_of_graphFlat K n h i

end FLT.Mazur.PolygonInfinitesimalStages
