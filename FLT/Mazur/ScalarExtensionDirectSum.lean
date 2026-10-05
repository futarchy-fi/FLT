/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Scalar extension of a full direct sum

The comparison retains the specified ring homomorphism and evaluates on each
homogeneous insertion. No finiteness of the index type is needed.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped DirectSum ChangeOfRings
namespace FLT.Mazur.ScalarExtensionDirectSum
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  {ι : Type*} [DecidableEq ι] (M : ι → ModuleCat R)

/-- Extension of scalars distributes over all homogeneous summands. -/
def comparison :
    (ModuleCat.extendScalars f).obj (ModuleCat.of R (⨁ i, M i)) ≅
      ModuleCat.of S (⨁ i, (ModuleCat.extendScalars f).obj (M i)) := by
  letI : Algebra R S := f.toAlgebra
  exact (TensorProduct.directSumRight R S S (fun i ↦ M i)).toModuleIso

/-- A scalar tensor with a homogeneous insertion remains in the same degree. -/
lemma comparison_tmul_lof (b : S) (i : ι) (m : M i) :
    (comparison f M).hom (b ⊗ₜ[R,f] DirectSum.lof R ι (fun i ↦ M i) i m) =
      DirectSum.lof S ι (fun i ↦ (ModuleCat.extendScalars f).obj (M i)) i
        (b ⊗ₜ[R,f] m) := by
  let : Algebra R S := f.toAlgebra
  exact TensorProduct.directSumRight_tmul_lof R S (M₂ := fun i ↦ M i) b i m

/-- The inverse comparison also retains the homogeneous insertion. -/
lemma comparison_inv_lof_tmul (b : S) (i : ι) (m : M i) :
    (comparison f M).inv
      (DirectSum.lof S ι (fun i ↦ (ModuleCat.extendScalars f).obj (M i)) i
        (b ⊗ₜ[R,f] m)) = b ⊗ₜ[R,f] DirectSum.lof R ι (fun i ↦ M i) i m := by
  rw [← comparison_tmul_lof]
  exact congrArg (fun k ↦ k (b ⊗ₜ[R,f] DirectSum.lof R ι (fun i ↦ M i) i m))
    (comparison f M).hom_inv_id

end FLT.Mazur.ScalarExtensionDirectSum
