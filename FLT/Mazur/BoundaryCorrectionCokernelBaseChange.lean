/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionBoundaryKernel
public import FLT.Mazur.CorrectionCokernelBaseChange

/-!
# Comparing the original and extended full boundary obstruction

The canonical full-cokernel comparison intertwines the actual boundary maps.
Consequently it carries the entire extended boundary image onto the scalar
extension of the original image, even without flatness.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
  (v : ∀ i, A i) (S : Type*) [CommRing S] [Algebra R S]
set_option quotPrecheck false
local notation "N" => ((∀ i, B i) × ∀ i j, C i j)
local notation "F" => originalCorrectionOperator φ p q v
local notation "FS" => ambientCorrectionOperator φ p q v S

/-- The ambient full cokernel is the scalar extension of the original full cokernel. -/
def boundaryCokernelBaseChangeEquiv :
    ((S ⊗[R] N) ⧸ LinearMap.range FS) ≃ₗ[S] S ⊗[R] (N ⧸ LinearMap.range F) :=
  (Submodule.quotEquivOfEq _ _
    (congrArg LinearMap.range (ambientCorrectionOperator_eq_baseChange φ p q v S))).trans
      (CorrectionCokernelBaseChange.equiv F S)

/-- Comparison on every pure equation tensor, with all mixed coordinates retained. -/
theorem boundaryCokernelBaseChangeEquiv_mk_tmul (s : S) (x : N) :
    boundaryCokernelBaseChangeEquiv φ p q v S ((LinearMap.range FS).mkQ (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] (LinearMap.range F).mkQ x := rfl

variable {D : Type*} [AddCommGroup D] [Module R D] (β : D →ₗ[R] (∀ i, B i))

/-- The comparison respects the full linear boundary map on arbitrary boundary tensors. -/
theorem boundaryCokernelBaseChangeEquiv_comp :
    (boundaryCokernelBaseChangeEquiv φ p q v S).toLinearMap.comp
      (boundaryCokernelMap φ p q v β S) =
        (originalBoundaryCokernelMap φ p q v β).baseChange S := by
  ext x
  rfl

/-- Comparison carries the extended image exactly onto the extension of the original image. -/
theorem boundaryCokernelBaseChangeEquiv_map_range :
    (LinearMap.range (boundaryCokernelMap φ p q v β S)).map
      (boundaryCokernelBaseChangeEquiv φ p q v S).toLinearMap =
        (LinearMap.range (originalBoundaryCokernelMap φ p q v β)).baseChange S := by
  rw [← LinearMap.range_comp, boundaryCokernelBaseChangeEquiv_comp,
    CompatibleErrorBaseChange.range_baseChange]

/-- The extended image is canonically the base-change submodule of the original image. -/
def boundaryImageBaseChangeEquiv :
    LinearMap.range (boundaryCokernelMap φ p q v β S) ≃ₗ[S]
      (LinearMap.range (originalBoundaryCokernelMap φ p q v β)).baseChange S :=
  (boundaryCokernelBaseChangeEquiv φ p q v S).ofSubmodules _ _
    (boundaryCokernelBaseChangeEquiv_map_range φ p q v S β)

end FLT.Mazur.BoundaryCorrectionIdeal
