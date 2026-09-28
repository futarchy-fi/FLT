/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import FLT.GroupScheme.HopfFrobenius
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The Hopf subalgebra of Frobenius powers

A subalgebra closed under comultiplication inherits a bialgebra structure over
a field. Closure under antipode gives a Hopf structure. Applied to Frobenius
images, this supplies actual structures and inclusion morphisms for induction.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Subalgebra

variable {k A : Type u} [Field k] [CommRing A] [Bialgebra k A]

/-- Comultiplication projected onto a subalgebra using a linear retraction. -/
def projectedComul (C : Subalgebra k A) : C →ₗ[k] C ⊗[k] C :=
  (TensorProduct.map C.val.toLinearMap.leftInverse C.val.toLinearMap.leftInverse).comp
    ((Coalgebra.comul (R := k)).comp C.val.toLinearMap)

/-- The projected comultiplication agrees with the ambient one whenever the
subalgebra is closed under comultiplication. -/
theorem map_projectedComul (C : Subalgebra k A)
    (hC : ∀ a ∈ C, Bialgebra.comulAlgHom k A a ∈
      (Algebra.TensorProduct.map C.val C.val).range) (c : C) :
    TensorProduct.map C.val.toLinearMap C.val.toLinearMap (C.projectedComul c) =
      Coalgebra.comul (R := k) (c : A) := by
  have hri : C.val.toLinearMap.leftInverse.comp C.val.toLinearMap = LinearMap.id :=
    LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨z, hz⟩ := hC c c.property
  change TensorProduct.map C.val.toLinearMap C.val.toLinearMap
    (TensorProduct.map C.val.toLinearMap.leftInverse C.val.toLinearMap.leftInverse
      (Coalgebra.comul (R := k) (c : A))) = _
  change TensorProduct.map C.val.toLinearMap C.val.toLinearMap z =
    Coalgebra.comul (R := k) (c : A) at hz
  rw [← hz]
  congr 1
  rw [TensorProduct.map_map, hri, TensorProduct.map_id]
  rfl

/-- Tensor squares of subalgebra inclusions over a field are injective. -/
theorem tensorSquare_val_injective (C : Subalgebra k A) :
    Function.Injective (TensorProduct.map C.val.toLinearMap C.val.toLinearMap) := by
  have hri : C.val.toLinearMap.leftInverse.comp C.val.toLinearMap = LinearMap.id :=
    LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  apply Function.LeftInverse.injective
    (g := TensorProduct.map C.val.toLinearMap.leftInverse C.val.toLinearMap.leftInverse)
  intro z
  rw [TensorProduct.map_map, hri, TensorProduct.map_id]
  rfl

/-- A subalgebra closed under comultiplication inherits a coalgebra structure. -/
@[instance_reducible]
def coalgebraOfComulMem (C : Subalgebra k A)
    (hC : ∀ a ∈ C, Bialgebra.comulAlgHom k A a ∈
      (Algebra.TensorProduct.map C.val C.val).range) : Coalgebra k C :=
  HopfAlgebra.IntegralClosure.Coalgebra.ofInjective k C A
    C.val.toLinearMap C.val.toLinearMap.leftInverse
    (LinearMap.leftInverse_comp_of_inj
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
    C.projectedComul ((Coalgebra.counit (R := k)).comp C.val.toLinearMap)
    (LinearMap.ext (C.map_projectedComul hC)) rfl

/-- A subalgebra closed under comultiplication inherits a bialgebra structure. -/
@[instance_reducible]
def bialgebraOfComulMem (C : Subalgebra k A)
    (hC : ∀ a ∈ C, Bialgebra.comulAlgHom k A a ∈
      (Algebra.TensorProduct.map C.val C.val).range) : Bialgebra k C := by
  let : Coalgebra k C := C.coalgebraOfComulMem hC
  apply Bialgebra.mk' k C
  · exact Bialgebra.counit_one (R := k) (A := A)
  · intro a b
    exact Bialgebra.counit_mul (R := k) (A := A) a.val b.val
  · apply C.tensorSquare_val_injective
    change TensorProduct.map C.val.toLinearMap C.val.toLinearMap
      (C.projectedComul 1) = _
    rw [C.map_projectedComul hC]
    change Coalgebra.comul (R := k) (1 : A) =
      Algebra.TensorProduct.map C.val C.val 1
    rw [Bialgebra.comul_one, map_one]
  · intro a b
    apply C.tensorSquare_val_injective
    change TensorProduct.map C.val.toLinearMap C.val.toLinearMap
      (C.projectedComul (a * b)) = _
    rw [C.map_projectedComul hC]
    change Coalgebra.comul (R := k) ((a : A) * (b : A)) =
      Algebra.TensorProduct.map C.val C.val (C.projectedComul a * C.projectedComul b)
    rw [Bialgebra.comul_mul, map_mul]
    change _ = TensorProduct.map C.val.toLinearMap C.val.toLinearMap (C.projectedComul a) *
      TensorProduct.map C.val.toLinearMap C.val.toLinearMap (C.projectedComul b)
    rw [C.map_projectedComul hC, C.map_projectedComul hC]

/-- The inclusion of a coproduct-stable subalgebra is a bialgebra homomorphism. -/
def valBialgHomOfComulMem (C : Subalgebra k A)
    (hC : ∀ a ∈ C, Bialgebra.comulAlgHom k A a ∈
      (Algebra.TensorProduct.map C.val C.val).range) :
    letI := C.bialgebraOfComulMem hC
    C →ₐc[k] A := by
  let := C.bialgebraOfComulMem hC
  exact BialgHom.ofAlgHom C.val rfl (AlgHom.ext fun c ↦ C.map_projectedComul hC c)

end Subalgebra

namespace Subalgebra

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]

/-- A subalgebra closed under comultiplication and antipode inherits the Hopf structure. -/
@[instance_reducible]
def hopfAlgebraOfClosed (C : Subalgebra k A)
    (hC : ∀ a ∈ C, Bialgebra.comulAlgHom k A a ∈
      (Algebra.TensorProduct.map C.val C.val).range)
    (hS : ∀ a ∈ C, HopfAlgebra.antipode k a ∈ C) : HopfAlgebra k C := by
  let : Bialgebra k C := C.bialgebraOfComulMem hC
  let S : C →ₗ[k] C :=
    ((HopfAlgebra.antipode k).comp C.val.toLinearMap).codRestrict
      C.toSubmodule (fun c ↦ hS c c.property)
  have hleft : C.val.toLinearMap.comp ((LinearMap.mul' k C).comp (S.rTensor C)) =
      ((LinearMap.mul' k A).comp ((HopfAlgebra.antipode k).rTensor A)).comp
        (TensorProduct.map C.val.toLinearMap C.val.toLinearMap) := by
    ext x y
    rfl
  have hright : C.val.toLinearMap.comp ((LinearMap.mul' k C).comp (S.lTensor C)) =
      ((LinearMap.mul' k A).comp ((HopfAlgebra.antipode k).lTensor A)).comp
        (TensorProduct.map C.val.toLinearMap C.val.toLinearMap) := by
    ext x y
    rfl
  refine
    { C.bialgebraOfComulMem hC with
      antipode := S
      mul_antipode_rTensor_comul := ?_
      mul_antipode_lTensor_comul := ?_ }
  · apply LinearMap.ext
    intro c
    apply Subtype.ext
    change (C.val.toLinearMap.comp ((LinearMap.mul' k C).comp (S.rTensor C)))
      (C.projectedComul c) = algebraMap k A (Coalgebra.counit (R := k) (c : A))
    rw [hleft, LinearMap.comp_apply, C.map_projectedComul hC]
    exact HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) (c : A)
  · apply LinearMap.ext
    intro c
    apply Subtype.ext
    change (C.val.toLinearMap.comp ((LinearMap.mul' k C).comp (S.lTensor C)))
      (C.projectedComul c) = algebraMap k A (Coalgebra.counit (R := k) (c : A))
    rw [hright, LinearMap.comp_apply, C.map_projectedComul hC]
    exact HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) (c : A)

end Subalgebra

namespace HopfAlgebra

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [PerfectRing k p]

/-- The Hopf structure on an iterated Frobenius image over a perfect field. -/
@[instance_reducible]
def frobeniusImageHopfAlgebra (n : ℕ) : HopfAlgebra k (Algebra.frobeniusImage k A p n) :=
  (Algebra.frobeniusImage k A p n).hopfAlgebraOfClosed
    (fun _ ha ↦ comul_mem_range_frobeniusImage p n ha)
    (fun _ ha ↦ antipode_mem_frobeniusImage p n ha)

/-- The Frobenius image inclusion, with its inherited Hopf structure, is a bialgebra map. -/
def frobeniusImageInclusion (n : ℕ) :
    letI := frobeniusImageHopfAlgebra (k := k) (A := A) p n
    Algebra.frobeniusImage k A p n →ₐc[k] A :=
  (Algebra.frobeniusImage k A p n).valBialgHomOfComulMem
    (fun _ ha ↦ comul_mem_range_frobeniusImage p n ha)

end HopfAlgebra
