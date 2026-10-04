/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CoactionTorsorGrading
public import FLT.GroupScheme.HopfPointFiberCoactionLaws
public import FLT.GroupScheme.HopfPointFiberLocalGenerator

/-!
# Strong grading from the canonical fibre torsor inverse

A multiplicative kernel basis compatible with the middle comultiplication gives
strong grading and a local homogeneous unit. Neither is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace HopfAlgebra

variable {R A B G : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra B A] [IsScalarTower R B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R) [Group G] [Finite G]
  (b : Module.Basis G R (A ⧸ augmentationIdeal f))
  (hone : b 1 = 1) (hmul : ∀ i j, b (i * j) = b i * b j)
  (hδ : CoactionBasis.diagonal b ∘ₗ (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap =
    TensorProduct.map (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap
      (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap ∘ₗ Coalgebra.comul)

include hone hmul hδ in
/-- The canonical inverse supplies one in the product of opposite components. -/
theorem pointFiber_one_mem_opposite_product (i : G) :
    (1 : PointFiber (A := A) p) ∈ pointFiberHomogeneous f hf p (b i⁻¹) *
      pointFiberHomogeneous f hf p (b i) :=
  CoactionBasis.one_mem_opposite_product b hone hmul (pointFiberCoaction f hf p)
    (fun i ↦ pointFiberHomogeneous f hf p (b i))
    (fun i x ↦ mem_pointFiberHomogeneous f hf p (b i) x)
    (pointFiberCoaction_coassoc f hf p b hδ) (pointFiberTorsorEquiv f hf p) (fun _ ↦ rfl) i

variable [Module.FaithfullyFlat B A]

include hone hmul hδ in
/-- Opposite homogeneous components multiply to the scalar submodule. -/
theorem pointFiber_opposite_product (i : G) :
    pointFiberHomogeneous f hf p (b i⁻¹) * pointFiberHomogeneous f hf p (b i) = 1 := by
  apply le_antisymm
  · have h := pointFiberHomogeneous_mul_le f hf p (b i⁻¹) (b i)
    simpa only [← hmul, inv_mul_cancel, hone, pointFiberHomogeneous_one] using h
  · exact Submodule.one_le.mpr
      (pointFiber_one_mem_opposite_product f hf p b hone hmul hδ i)

include hone hmul hδ in
/-- Every pair of homogeneous components has the full product component. -/
theorem pointFiber_strong_grading (i j : G) :
    pointFiberHomogeneous f hf p (b i) * pointFiberHomogeneous f hf p (b j) =
      pointFiberHomogeneous f hf p (b (i * j)) := by
  apply le_antisymm
  · simpa only [hmul] using pointFiberHomogeneous_mul_le f hf p (b i) (b j)
  · calc
      pointFiberHomogeneous f hf p (b (i * j)) =
          pointFiberHomogeneous f hf p (b (i * j)) * 1 := (mul_one _).symm
      _ = pointFiberHomogeneous f hf p (b (i * j)) *
          (pointFiberHomogeneous f hf p (b j⁻¹) * pointFiberHomogeneous f hf p (b j)) := by
        rw [pointFiber_opposite_product f hf p b hone hmul hδ j]
      _ = (pointFiberHomogeneous f hf p (b (i * j)) *
          pointFiberHomogeneous f hf p (b j⁻¹)) * pointFiberHomogeneous f hf p (b j) :=
        (mul_assoc _ _ _).symm
      _ ≤ pointFiberHomogeneous f hf p (b i) * pointFiberHomogeneous f hf p (b j) := by
        refine mul_le_mul' ?_ le_rfl
        simpa only [← hmul, mul_inv_cancel_right] using
          pointFiberHomogeneous_mul_le f hf p (b (i * j)) (b j⁻¹)

/-- Basis degrees are units, constructed from the group law. -/
def pointFiberDegreeUnit (i : G) : (A ⧸ augmentationIdeal f)ˣ where
  val := b i
  inv := b i⁻¹
  val_inv := by rw [← hmul, mul_inv_cancel, hone]
  inv_val := by rw [← hmul, inv_mul_cancel, hone]

omit [Module.FaithfullyFlat B A] in
include hδ in
/-- The W45 generator obligation follows from the canonical torsor inverse. -/
theorem pointFiber_degree_strong (i : G) :
    (1 : PointFiber (A := A) p) ∈
      pointFiberHomogeneous f hf p (pointFiberDegreeUnit f b hone hmul i : A ⧸ _) *
      pointFiberHomogeneous f hf p (↑(pointFiberDegreeUnit f b hone hmul i)⁻¹) := by
  change (1 : PointFiber (A := A) p) ∈ pointFiberHomogeneous f hf p (b i) *
    pointFiberHomogeneous f hf p (b i⁻¹)
  rw [mul_comm]
  exact pointFiber_one_mem_opposite_product f hf p b hone hmul hδ i

variable [IsLocalRing R]

include hone hmul hδ in
/-- A local multiplicative fibre has a homogeneous unit spanning each component. -/
theorem pointFiber_exists_homogeneous_unit (i : G) :
    ∃ z : (PointFiber (A := A) p)ˣ,
      (z : PointFiber (A := A) p) ∈ pointFiberHomogeneous f hf p (b i) ∧
      Submodule.span R {(z : PointFiber (A := A) p)} =
        pointFiberHomogeneous f hf p (b i) := by
  let t := pointFiberDegreeUnit f b hone hmul i
  have hs := pointFiber_degree_strong f hf p b hone hmul hδ i
  exact ⟨pointFiberLocalGenerator f hf p t hs,
    pointFiberLocalGenerator_mem f hf p t hs,
    pointFiberLocalGenerator_span f hf p t hs⟩

end HopfAlgebra
