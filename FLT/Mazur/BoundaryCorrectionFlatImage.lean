/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionCokernelBaseChange

/-!
# Flat scalar extension of the exact boundary obstruction image

For flat scalars the extended image is the tensor of the original image,
and hence the tensor of the boundary parameters modulo the exact original
kernel. No finiteness of the parameter module is used.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
  (v : ∀ i, A i) {D : Type*} [AddCommGroup D] [Module R D]
  (β : D →ₗ[R] (∀ i, B i)) (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]
set_option quotPrecheck false
local notation "g" => originalBoundaryCokernelMap φ p q v β
local notation "gS" => boundaryCokernelMap φ p q v β S

/-- Flatness identifies the tensor of the exact original image with the full extended image. -/
def boundaryImageTensorEquiv : (S ⊗[R] LinearMap.range g) ≃ₗ[S] LinearMap.range gS :=
  (Submodule.toBaseChange.toLinearEquiv S (LinearMap.range g)).trans
    (boundaryImageBaseChangeEquiv φ p q v S β).symm

/-- The original boundary quotient is a canonical presentation of the extended image. -/
def boundaryQuotientTensorEquiv :
    (S ⊗[R] (D ⧸ LinearMap.ker g)) ≃ₗ[S] LinearMap.range gS :=
  ((g).quotKerEquivRange.baseChange R S _ _).trans
    (boundaryImageTensorEquiv φ p q v β S)

/-- Under comparison, a tensor of an original image element is its ambient pure tensor. -/
theorem boundaryImageTensorEquiv_compare_tmul (s : S) (x : LinearMap.range g) :
    boundaryCokernelBaseChangeEquiv φ p q v S
      (boundaryImageTensorEquiv φ p q v β S (s ⊗ₜ[R] x)) = s ⊗ₜ[R] x.val := by
  change (boundaryCokernelBaseChangeEquiv φ p q v S)
    ((boundaryImageBaseChangeEquiv φ p q v S β).symm
      (Submodule.toBaseChange.toLinearEquiv S (LinearMap.range g) (s ⊗ₜ[R] x))) = _
  rw [show ∀ y, (boundaryCokernelBaseChangeEquiv φ p q v S)
      ((boundaryImageBaseChangeEquiv φ p q v S β).symm y) = y.val from
    fun y ↦ congrArg Subtype.val
      ((boundaryImageBaseChangeEquiv φ p q v S β).apply_symm_apply y)]
  rfl

/-- The quotient comparison sends the class of a boundary parameter to its actual obstruction. -/
theorem boundaryQuotientTensorEquiv_mk_tmul (s : S) (t : D) :
    (boundaryQuotientTensorEquiv φ p q v β S
      (s ⊗ₜ[R] (LinearMap.ker g).mkQ t)).val = gS (s ⊗ₜ[R] t) := by
  apply (boundaryCokernelBaseChangeEquiv φ p q v S).injective
  change (boundaryCokernelBaseChangeEquiv φ p q v S)
    (boundaryImageTensorEquiv φ p q v β S (s ⊗ₜ[R] (g).rangeRestrict t)) = _
  rw [boundaryImageTensorEquiv_compare_tmul, boundaryCokernelMap_tmul,
    boundaryCokernelBaseChangeEquiv_mk_tmul]
  rfl

end FLT.Mazur.BoundaryCorrectionIdeal
