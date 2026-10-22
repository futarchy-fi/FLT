/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeProjective
public import FLT.Mazur.FiniteGroupFreeTensorInvariants

/-!
# Detecting full orbit tensors by their group coordinates

Trace dual generators reconstruct every tensor, including nilpotent tensors.
The orbit comparison is therefore injective for a free finite action. The
base is the actual fixed ring; replacing it by a smaller scalar ring requires
an additional comparison.
-/

@[expose] public noncomputable section
open TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] [Fintype G]
  (A : Type*) [CommRing A] [MulSemiringAction G A]
local notation "S" => invariantRing G A
local notation "C" => A ⊗[S] A

/-- Evaluation of an orbit tensor at one group element. -/
def orbitTensorCoordinate (g : G) : C →ₐ[S] A :=
  Algebra.TensorProduct.productMap (AlgHom.id S A) (MulSemiringAction.toAlgHom S A g)

omit [Fintype G] in
/-- Coordinates keep both original factors of a pure tensor. -/
@[simp] theorem orbitTensorCoordinate_tmul (g : G) (a b : A) :
    orbitTensorCoordinate G A g (a ⊗ₜ[S] b) = a * (g • b) := rfl

/-- A weighted trace contraction is the weighted sum of all orbit coordinates. -/
theorem orbitTensor_trace_contraction (b : A) (t : C) :
    invariantTensorRetraction G A A b t =
      ∑ g : G, (g • b) * orbitTensorCoordinate G A g t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [invariantTensorRetraction_tmul]
    change (∑ g : G, g • (b * y)) * x = _
    simp only [Finset.sum_mul, MulSemiringAction.smul_mul, orbitTensorCoordinate_tmul]
    apply Finset.sum_congr rfl
    intro g _
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add, Finset.sum_add_distrib]

/-- The finite trace dual system reconstructs the full tensor, not only its residue image. -/
theorem orbitTensor_reconstruct (s : Finset A) (a : A → A)
    (ha : ∀ x : A, ∑ b ∈ s, weightedTraceLinear G b x • a b = x) (t : C) :
    ∑ b ∈ s, invariantTensorRetraction G A A b t ⊗ₜ[S] a b = t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [invariantTensorRetraction_tmul, TensorProduct.smul_tmul]
    change ∑ b ∈ s, x ⊗ₜ[S] (weightedTraceLinear G b y • a b) = x ⊗ₜ[S] y
    rw [← TensorProduct.tmul_sum, ha]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

omit [Fintype G] in
/-- Scheme-theoretic freeness makes the actual orbit coordinates detect all tensors. -/
theorem orbitTensorCoordinate_ext [Finite G]
    (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤) {x y : C}
    (h : ∀ g, orbitTensorCoordinate G A g x = orbitTensorCoordinate G A g y) : x = y := by
  let _ := Fintype.ofFinite G
  obtain ⟨s, a, ha⟩ := exists_trace_dual_generators G hfree
  rw [← orbitTensor_reconstruct G A s a ha x, ← orbitTensor_reconstruct G A s a ha y]
  apply Finset.sum_congr rfl
  intro b _
  rw [orbitTensor_trace_contraction, orbitTensor_trace_contraction]
  simp only [h]

end FLT.Mazur.FiniteGroupQuotient
