/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-! # Flat extension of an ideal as a module base change -/

@[expose] public noncomputable section

open TensorProduct

namespace Ideal

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

/-- Under the tensor unit identification, the scalar extension of an ideal is its mapped ideal. -/
theorem map_baseChange_rid (I : Ideal R) :
    (I.baseChange S).map (AlgebraTensorModule.rid R S S).toLinearMap =
      I.map (algebraMap R S) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, ← Set.image_comp]
  change Submodule.span S _ = Submodule.span S _
  congr 1
  apply Set.image_congr
  intro x _
  simp [Algebra.smul_def]

/-- Flatness identifies the tensor of an ideal with the actual extended ideal. -/
def tensorMapEquiv [Module.Flat R S] (I : Ideal R) :
    S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
  (Submodule.toBaseChange.toLinearEquiv S I).trans
    (((AlgebraTensorModule.rid R S S).submoduleMap (I.baseChange S)).trans
      (LinearEquiv.ofEq _ _ (map_baseChange_rid S I)))

/-- The ideal comparison preserves every original element. -/
@[simp] theorem tensorMapEquiv_one_tmul [Module.Flat R S] (I : Ideal R) (x : I) :
    tensorMapEquiv S I (1 ⊗ₜ x) = Algebra.idealMap S I x := by
  apply Subtype.ext
  simp [tensorMapEquiv, Algebra.smul_def]

/-- The canonical ideal map is a base change when the coefficient algebra is flat. -/
theorem isBaseChange_idealMap [Module.Flat R S] (I : Ideal R) :
    IsBaseChange S (Algebra.idealMap S I) :=
  IsBaseChange.of_equiv (tensorMapEquiv S I) (tensorMapEquiv_one_tmul S I)

end Ideal
