/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Free

/-! # Complete coefficients in a finite free tensor module -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace AdicCompletion
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (I : Ideal R)

/-- Adic completion is already the original module when coordinates form a finite
product of a complete coefficient module. -/
def finiteCoordinatesEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsAdicComplete I N] (e : M ≃ₗ[R] (ι → N)) : AdicCompletion I M ≃ₗ[R] M :=
  ((congr I e).restrictScalars R).trans
    (((piEquivOfFintype I (fun _ : ι ↦ N)).restrictScalars R).trans
      ((LinearEquiv.piCongrRight (fun _ ↦ (ofLinearEquiv I N).symm)).trans e.symm))

/-- The finite-coordinate comparison inverts the canonical completion map. -/
theorem finiteCoordinatesEquiv_of {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsAdicComplete I N] (e : M ≃ₗ[R] (ι → N)) (x : M) :
    finiteCoordinatesEquiv I e (of I M x) = x := by
  apply e.injective
  simp only [finiteCoordinatesEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.apply_symm_apply]
  change (LinearEquiv.piCongrRight (fun _ : ι ↦ (ofLinearEquiv I N).symm))
    (piEquivOfFintype I (fun _ : ι ↦ N) (congr I e (of I M x))) = e x
  ext i
  simp [piEquivOfFintype_apply, pi, map_of]

/-- Finite free coordinates over complete coefficients give actual adic completeness. -/
theorem isAdicComplete_of_finite_coordinates {ι : Type*} [Finite ι]
    [IsAdicComplete I N] (e : M ≃ₗ[R] (ι → N)) : IsAdicComplete I M := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply of_bijective_iff.mp
  have he : (finiteCoordinatesEquiv I e).toLinearMap.comp (of I M) = LinearMap.id :=
    LinearMap.ext (finiteCoordinatesEquiv_of I e)
  have hb : Function.Bijective ((finiteCoordinatesEquiv I e).toLinearMap.comp (of I M)) := by
    rw [he]
    exact Function.bijective_id
  exact (finiteCoordinatesEquiv I e).bijective.of_comp_iff' _ |>.mp hb

variable {S : Type*} [CommRing S] [Algebra R S] [StrongRankCondition R]
  [Module.Free R M] [Module.Finite R M]

/-- A finite free original module tensor complete coefficients needs no further completion. -/
theorem finiteFree_tensor_isAdicComplete [IsAdicComplete I S] :
    IsAdicComplete I (M ⊗[R] S) := by
  classical
  let e : M ⊗[R] S ≃ₗ[R] (Fin (Module.finrank R M) → S) :=
    (TensorProduct.comm R M S).trans
      (((Module.finBasis R M).baseChange S).equivFun.restrictScalars R)
  exact isAdicComplete_of_finite_coordinates I e
end AdicCompletion
