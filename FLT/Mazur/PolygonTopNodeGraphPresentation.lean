/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphAlgebra
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The full higher graph ideal in the original node product

Evaluation of the two node factors on both full Laurent branches has
exactly the source-target graph as its range. Its full kernel presents
the graph ring, without replacing either node equation or taking radicals.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal topNodeGraphAlgebra
variable (R : Type) [CommRing R] (m : ℕ)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ)
local notation "S" => Ring R (m + 1)
local notation "B" => ChartRing (parameter R (m + 1))
local notation "L" => (S)[T;T⁻¹]
local notation "β" => stageNodeBranchPair R (m + 1)
local notation "F" => stageNodeBranchSubstitution R (m + 1) u v
local notation "G" => topNodeGraphAlgebra R m u v

/-- Cache the original graph ring before constructing its quotient presentation. -/
local instance topGraphPresentationCommRing : CommRing (G) := inferInstance

/-- Cache the original tensor ring without unfolding the node factors again. -/
local instance topGraphPresentationTensorCommRing : CommRing ((B) ⊗[S] (B)) := inferInstance

/-- The full source-target evaluation on the original product of smoothing nodes. -/
def topNodeGraphPairMap : (B) ⊗[S] (B) →ₐ[S] ((L) × (L)) :=
  Algebra.TensorProduct.productMap (β) ((F).comp (β))

/-- The range is exactly the actual source-target graph, before any reduction. -/
theorem topNodeGraphPairMap_range : (topNodeGraphPairMap R m u v).range = (G) := by
  rw [topNodeGraphPairMap, Algebra.TensorProduct.productMap_range, topNodeGraphAlgebra]
  rfl

/-- The original node-product algebra maps onto the entire graph algebra. -/
def topNodeGraphTensorMap : (B) ⊗[S] (B) →ₐ[S] (G) :=
  (topNodeGraphPairMap R m u v).codRestrict (G) (fun z ↦ by
    rw [← topNodeGraphPairMap_range]
    exact ⟨z, rfl⟩)

/-- Tensor evaluation retains both original punctured-branch values. -/
theorem topNodeGraphTensorMap_val (z : (B) ⊗[S] (B)) :
    (topNodeGraphTensorMap R m u v z).val = topNodeGraphPairMap R m u v z := rfl

/-- No graph function is missing from the original node-product presentation. -/
theorem topNodeGraphTensorMap_surjective :
    Function.Surjective (topNodeGraphTensorMap R m u v) := by
  intro z
  have hz : z.val ∈ (topNodeGraphPairMap R m u v).range := by
    rw [topNodeGraphPairMap_range]
    exact z.property
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, Subtype.ext hw⟩

/-- The actual full defining ideal of the original two-node correspondence. -/
def topNodeGraphIdeal : Ideal ((B) ⊗[S] (B)) :=
  RingHom.ker (topNodeGraphPairMap R m u v).toRingHom

/-- The same full ideal is the kernel of the surjection onto the graph. -/
theorem topNodeGraphIdeal_eq :
    topNodeGraphIdeal R m u v = RingHom.ker (topNodeGraphTensorMap R m u v).toRingHom := by
  ext z
  change topNodeGraphPairMap R m u v z = 0 ↔ topNodeGraphTensorMap R m u v z = 0
  rw [← topNodeGraphTensorMap_val]
  exact ⟨fun hz ↦ Subtype.ext hz, fun hz ↦ congrArg Subtype.val hz⟩

/-- Quotienting by the unchanged full kernel gives the entire graph ring. -/
def topNodeGraphQuotientEquiv : ((B) ⊗[S] (B)) ⧸ topNodeGraphIdeal R m u v ≃+* (G) :=
  (Ideal.quotEquivOfEq (topNodeGraphIdeal_eq R m u v)).trans
    (RingHom.quotientKerEquivOfSurjective (topNodeGraphTensorMap_surjective R m u v))

end FLT.Mazur.PolygonInfinitesimalStages
