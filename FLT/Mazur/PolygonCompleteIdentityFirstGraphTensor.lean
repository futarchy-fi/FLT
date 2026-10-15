/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphScheme
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The original first graph is a quotient of the original node product

The source and unchanged action together generate exactly the finite graph
algebra. Thus the correspondence has an actual closed presentation in the
original node product, with its full kernel rather than its radical.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "B" => ChartRing (parameter (R) 1)
local notation "L" => (S)[T;T⁻¹]
local notation "β" => firstNodeBranchPair (R)
local notation "F" => completeIdentityFirstActionBranchEquiv K n h i
local notation "E" => completeIdentityFirstErrorAlgebra K n h i

/-- Original source-target evaluation on the two entire punctured branches. -/
def completeIdentityFirstGraphPairMap : (B) ⊗[S] (B) →ₐ[S] ((L) × (L)) :=
  Algebra.TensorProduct.productMap (β) ((F).toAlgHom.comp (β))

/-- Its range is the actual finite graph algebra, without reducing any ideal. -/
theorem completeIdentityFirstGraphPairMap_range :
    (completeIdentityFirstGraphPairMap K n h i).range =
      (E).restrictScalars (S) := by
  rw [completeIdentityFirstErrorAlgebra_eq_graph, completeIdentityFirstGraphPairMap,
    Algebra.TensorProduct.productMap_range]
  rfl

/-- The node-product coordinate ring surjects onto the unchanged original graph. -/
def completeIdentityFirstGraphTensorMap : (B) ⊗[S] (B) →ₐ[S] (E) :=
  (completeIdentityFirstGraphPairMap K n h i).codRestrict ((E).restrictScalars (S))
    (fun z ↦ by
      rw [← completeIdentityFirstGraphPairMap_range]
      exact ⟨z, rfl⟩)

/-- Tensor evaluation retains both original branch values. -/
theorem completeIdentityFirstGraphTensorMap_val (z : (B) ⊗[S] (B)) :
    (completeIdentityFirstGraphTensorMap K n h i z).val =
      completeIdentityFirstGraphPairMap K n h i z := rfl

/-- Every actual graph function is an original node-product function. -/
theorem completeIdentityFirstGraphTensorMap_surjective :
    Function.Surjective (completeIdentityFirstGraphTensorMap K n h i) := by
  intro z
  have hz : z.val ∈ (completeIdentityFirstGraphPairMap K n h i).range := by
    rw [completeIdentityFirstGraphPairMap_range]
    exact z.property
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, Subtype.ext hw⟩

/-- The first original product coordinate is exactly the constructed source map. -/
theorem completeIdentityFirstGraphTensorMap_left (z : B) :
    completeIdentityFirstGraphTensorMap K n h i (z ⊗ₜ 1) =
      completeIdentityFirstGraphSource K n h i z := by
  apply Subtype.ext
  exact Algebra.TensorProduct.productMap_left_apply _ _ z

/-- The second original product coordinate is exactly the unchanged action target. -/
theorem completeIdentityFirstGraphTensorMap_right (z : B) :
    completeIdentityFirstGraphTensorMap K n h i (1 ⊗ₜ z) =
      completeIdentityFirstGraphTarget K n h i z := by
  apply Subtype.ext
  exact Algebra.TensorProduct.productMap_right_apply _ _ z

end FLT.Mazur.PolygonInfinitesimalStages
