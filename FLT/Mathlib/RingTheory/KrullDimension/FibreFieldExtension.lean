/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.KrullDimension.FieldBaseChange
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.FiniteStability

/-! # Fibre dimension and the residue-field comparison between coefficient stages -/

@[expose] public noncomputable section

open scoped TensorProduct

/-- The dimension of a finite-type fibre is unchanged after further field extension. -/
theorem ringKrullDim_fibre_field_extension (R A k K : Type*) [CommRing R] [CommRing A]
    [Field k] [Field K] [Algebra R A] [Algebra.FiniteType R A]
    [Algebra R k] [Algebra R K] [Algebra k K] [IsScalarTower R k K] :
    ringKrullDim (K ⊗[R] A) = ringKrullDim (k ⊗[R] A) := by
  rw [← ringKrullDim_eq_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R k K K A).toRingEquiv]
  exact ringKrullDim_tensorProduct_field k K (k ⊗[R] A)

/-- Contracting a prime along a coefficient-stage map gives the exact residue-field
comparison needed to transfer fibre-dimension bounds back to that stage. -/
theorem ringKrullDim_fibre_residue_extension (R S A : Type*) [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] [Algebra.FiniteType R A]
    (q : Ideal S) [q.IsPrime] :
    ringKrullDim (q.ResidueField ⊗[R] A) =
      ringKrullDim ((q.comap (algebraMap R S)).ResidueField ⊗[R] A) := by
  let p := q.comap (algebraMap R S)
  let φ := Ideal.ResidueField.map p q (algebraMap R S) rfl
  let : Algebra p.ResidueField q.ResidueField := φ.toAlgebra
  have : IsScalarTower R p.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R q.ResidueField r = φ (algebraMap R p.ResidueField r)
      rw [Ideal.ResidueField.map_algebraMap]
      exact IsScalarTower.algebraMap_apply R S q.ResidueField r
  exact ringKrullDim_fibre_field_extension R A p.ResidueField q.ResidueField

end
