/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupTraceRetraction
public import FLT.Mazur.InvariantFlatTensorAction

/-!
# Arbitrary coefficient base change for free finite-group invariants

Weighted trace gives an explicit inverse to the scalar invariant comparison.
The coefficient algebra may have arbitrary nilpotents and need not be flat.
-/

@[expose] public noncomputable section
open TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G A : Type*) [Group G] [Fintype G] [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra (invariantRing G A) B]
local notation "S" => invariantRing G A
local notation "C" => B ⊗[S] A

/-- The original weighted trace extends linearly to every coefficient algebra. -/
def invariantTensorRetraction (a : A) : C →ₗ[S] B :=
  (TensorProduct.rid S B).toLinearMap.comp ((weightedTraceLinear G a).lTensor B)

/-- The coefficient formula on actual pure tensors. -/
theorem invariantTensorRetraction_tmul (a x : A) (b : B) :
    invariantTensorRetraction G A B a (b ⊗ₜ[S] x) = orbitTrace G (a * x) • b := rfl

/-- A trace-one weight recovers every original coefficient after arbitrary base change. -/
theorem invariantTensorRetraction_scalar (a : A) (ha : orbitTrace G a = 1) (b : B) :
    invariantTensorRetraction G A B a (algebraMap B C b) = b := by
  change orbitTrace G (a * 1) • b = b
  rw [mul_one, ha, one_smul]

attribute [local instance] tensorAction

/-- The extended retraction is the weighted orbit sum on the actual tensor ring. -/
theorem invariantTensorRetraction_sum (a : A) (x : C) :
    algebraMap B C (invariantTensorRetraction G A B a x) =
      ∑ g : G, (1 ⊗ₜ[S] (g • a)) * (g • x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
    simp only [invariantTensorRetraction_tmul, Algebra.TensorProduct.algebraMap_apply]
    change (orbitTrace G (a * x) • b) ⊗ₜ[S] (1 : A) =
      ∑ g : G, (1 ⊗ₜ[S] (g • a)) * (b ⊗ₜ[S] (g • x))
    rw [TensorProduct.smul_tmul]
    simp only [Algebra.smul_def, mul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change b ⊗ₜ[S] (∑ g : G, g • (a * x)) = _
    rw [TensorProduct.tmul_sum]
    simp only [MulSemiringAction.smul_mul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add, mul_add, Finset.sum_add_distrib]

/-- On invariant tensors a trace-one retraction recovers the entire original element. -/
theorem invariantTensorRetraction_fixed (a : A) (ha : orbitTrace G a = 1)
    (x : invariantRing G C) :
    algebraMap B C (invariantTensorRetraction G A B a x.val) = x.val := by
  rw [invariantTensorRetraction_sum]
  have hx (g : G) : g • x.val = x.val := x.property g
  simp only [hx, ← Finset.sum_mul, ← TensorProduct.tmul_sum]
  have h : ∑ g : G, g • a = (1 : A) := congrArg Subtype.val ha
  rw [h, ← Algebra.TensorProduct.one_def, one_mul]

omit [Fintype G] in
/-- Freeness makes the actual invariant comparison bijective for arbitrary coefficients. -/
theorem tensorInvariantMap_bijective_of_free [Finite G]
    (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤) :
    Function.Bijective (tensorInvariantMap G A B) := by
  let _ := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := exists_orbitTrace_one G hfree
  constructor
  · intro b c h
    have he := congrArg (fun x : invariantRing G C ↦
      invariantTensorRetraction G A B a x.val) h
    simpa only [tensorInvariantMap_val, invariantTensorRetraction_scalar G A B a ha] using he
  · intro x
    exact ⟨invariantTensorRetraction G A B a x.val,
      Subtype.ext (invariantTensorRetraction_fixed G A B a ha x)⟩

omit [Fintype G] in
/-- The full fixed ring after base change is the original coefficient ring, with its nilpotents. -/
def freeTensorInvariantEquiv [Finite G]
    (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤) : B ≃+* invariantRing G C :=
  RingEquiv.ofBijective (tensorInvariantMap G A B)
    (tensorInvariantMap_bijective_of_free G A B hfree)

end FLT.Mazur.FiniteGroupQuotient
