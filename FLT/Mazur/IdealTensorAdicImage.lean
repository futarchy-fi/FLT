/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleIdealTensorFinite
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Adic bounds on ideal-tensor images

An internal multiple of the base ideal gives an internal multiple of its
tensor module over the actual extended ideal in the target algebra.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorAdicImage
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Internal ideal multiples remain internal after tensoring and extending scalars. -/
theorem tmul_mem (A I : Ideal R) (m : M) (a : I) (ha : a.val ∈ A • I) :
    m ⊗ₜ[R] a ∈ (A.map (algebraMap R S)) • (⊤ : Submodule S (M ⊗[R] I)) := by
  have ha' := (Submodule.mem_smul_top_iff A I a).mpr ha
  refine Submodule.smul_induction_on ha' ?_ ?_
  · intro r hr b _
    rw [tmul_smul, ← IsScalarTower.algebraMap_smul S r]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) (Submodule.mem_top)
  · intro x y hx hy
    rw [tmul_add]
    exact Submodule.add_mem _ hx hy

/-- The entire tensor image has the bound, not just its pure tensors. -/
theorem inclusion_mem (A I K : Ideal R) (hKI : K ≤ I) (hK : K ≤ A • I)
    (z : M ⊗[R] K) :
    (Submodule.inclusion hKI).lTensor M z ∈
      (A.map (algebraMap R S)) • (⊤ : Submodule S (M ⊗[R] I)) := by
  induction z with
  | tmul m a => exact tmul_mem A I m ⟨a.val, hKI a.property⟩ (hK a.property)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

end FLT.Mazur.IdealTensorAdicImage
