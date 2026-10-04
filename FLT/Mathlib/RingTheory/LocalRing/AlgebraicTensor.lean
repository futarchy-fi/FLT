/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Algebraic coefficient extension of a local algebra with rational residue field -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

/-- An integral algebra is local if the extension of the original maximal ideal is maximal. -/
theorem of_isIntegral_of_map_maximal [Algebra.IsIntegral R S]
    [(maximalIdeal R |>.map (algebraMap R S)).IsMaximal] : IsLocalRing S := by
  let J := (maximalIdeal R).map (algebraMap R S)
  refine of_unique_max_ideal ⟨J, inferInstance, fun P hP ↦ ?_⟩
  have : P.IsMaximal := hP
  have hP' : P.under R = maximalIdeal R := eq_maximalIdeal inferInstance
  have hle : J ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hP'.ge
  exact (Ideal.IsMaximal.eq_of_le (I := J) inferInstance hP.ne_top hle).symm

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Algebra k R]

/-- A rational residue field stays a field after extending coefficients. -/
def tensorResidueEquiv (e : (R ⧸ maximalIdeal R) ≃ₐ[k] k) :
    ((R ⊗[k] K) ⧸ (maximalIdeal R).map (algebraMap R (R ⊗[k] K))) ≃ₐ[k] K :=
  (Algebra.TensorProduct.quotientTensorEquiv (R := k) k K R (maximalIdeal R)).symm.trans
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl : K ≃ₐ[k] K)).trans
      (Algebra.TensorProduct.lid k K))

/-- An algebraic field extension preserves locality when the residue field is the base field. -/
theorem tensor_isLocalRing [Algebra.IsAlgebraic k K]
    (e : (R ⧸ maximalIdeal R) ≃ₐ[k] k) : IsLocalRing (R ⊗[k] K) := by
  have : ((maximalIdeal R).map (algebraMap R (R ⊗[k] K))).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ ((tensorResidueEquiv (K := K) e).toRingEquiv.isField
      (Field.toIsField K))
  exact of_isIntegral_of_map_maximal (R := R)

end IsLocalRing
