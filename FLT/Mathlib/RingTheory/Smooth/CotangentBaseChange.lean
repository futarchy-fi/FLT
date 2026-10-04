/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Cotangent base change with the target algebra as scalars

The flat base-change theorem for the first cotangent homology can also be
read over the tensor-product algebra, rather than just over the new base.
-/

public noncomputable section

open TensorProduct

section

variable {R T S B M N : Type*} [CommRing R] [CommRing T] [CommRing S] [CommRing B]
    [Algebra R T] [Algebra R S] [Algebra R B] [Algebra S B] [Algebra T B]
    [IsScalarTower R S B] [IsScalarTower R T B] [Algebra.IsPushout R T S B]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [Module T N] [Module B N]
    [IsScalarTower R S N] [IsScalarTower R T N] [IsScalarTower R B N]
    [IsScalarTower S B N] [IsScalarTower T B N]

/-- A module base change over a pushout can be read using the target algebra as scalars. -/
theorem IsBaseChange.of_restrictScalars_of_isPushout (f : M →ₗ[S] N)
    (h : IsBaseChange T (f.restrictScalars R)) : IsBaseChange B f := by
  let e := Algebra.IsPushout.cancelBaseChange R T S B M
  have he : ((f.liftBaseChange B).restrictScalars T).comp e.symm.toLinearMap =
      h.equiv.toLinearMap := by
    ext t
    simp [e, IsBaseChange.equiv_tmul]
  change Function.Bijective (f.liftBaseChange B)
  have hb : Function.Bijective ((f.liftBaseChange B) ∘ e.symm) := by
    change Function.Bijective (((f.liftBaseChange B).restrictScalars T).comp e.symm.toLinearMap)
    rw [he]
    exact h.equiv.bijective
  exact (Function.Bijective.of_comp_iff _ e.symm.bijective).mp hb

end

namespace Algebra

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

attribute [local instance] TensorProduct.rightAlgebra in
/-- Flat base change of first cotangent homology, as a module over the tensor algebra. -/
theorem H1Cotangent.isBaseChange_tensorProduct [Module.Flat R T] :
    IsBaseChange (T ⊗[R] S) (H1Cotangent.map R T S (T ⊗[R] S)) := by
  apply IsBaseChange.of_restrictScalars_of_isPushout (R := R) (T := T)
  apply IsBaseChange.of_equiv (tensorH1CotangentOfFlat R S T)
  intro x
  simp [tensorH1CotangentOfFlat_tmul]

attribute [local instance] TensorProduct.rightAlgebra in
/-- Differentials commute with base change as modules over the tensor algebra. -/
theorem kaehler_isBaseChange_tensorProduct :
    IsBaseChange (T ⊗[R] S) (KaehlerDifferential.map R T S (T ⊗[R] S)) := by
  apply IsBaseChange.of_restrictScalars_of_isPushout (R := R) (T := T)
  exact KaehlerDifferential.isBaseChange R T S (T ⊗[R] S)

end Algebra
