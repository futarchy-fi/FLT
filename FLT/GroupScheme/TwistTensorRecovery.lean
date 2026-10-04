/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TensorScalarComparison
public import FLT.GroupScheme.TwistTensorMaps

/-!
# Effective tensor descent from scalar recovery

Faithful flatness and scalar recovery for the two factors and their tensor
product prove that the canonical fixed-algebra tensor comparison is invertible.
The arithmetic specialization supplies all three recovery proofs.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable {R S H J : Type u} {G : Type*}
  [CommRing R] [CommRing S] [CommRing H] [CommRing J]
  [Algebra R S] [Algebra R H] [Algebra R J] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))
  (υ : G →* (J ≃ₐ[R] J))

/-- Recovery, regarded over the splitting coefficient ring. -/
def twistRecoveryEquiv (h : Function.Bijective (recoveryMap (S := S) (twistAction σ τ))) :
    S ⊗[R] twistModel σ τ ≃ₐ[S] S ⊗[R] H where
  __ := (AlgEquiv.ofBijective (recoveryMap (S := S) (twistAction σ τ)) h).toRingEquiv
  commutes' _ := mul_one _

/-- Recovery multiplies the splitting coefficient into an invariant. -/
theorem twistRecoveryEquiv_tmul
    (h : Function.Bijective (recoveryMap (S := S) (twistAction σ τ)))
    (s : S) (x : twistModel σ τ) :
    twistRecoveryEquiv σ τ h (s ⊗ₜ[R] x) = s • x.val := by
  exact (Algebra.smul_def s x.val).symm

variable
  (hH : Function.Bijective (recoveryMap (S := S) (twistAction σ τ)))
  (hJ : Function.Bijective (recoveryMap (S := S) (twistAction σ υ)))
  (hHJ : Function.Bijective (recoveryMap (S := S) (twistAction σ (twistAction τ υ))))

/-- The scalar extension of the tensor comparison, expressed through recovery. -/
def recoveredTensorEquiv :
    S ⊗[R] (twistModel σ τ ⊗[R] twistModel σ υ) ≃ₐ[S]
      S ⊗[R] twistModel σ (twistAction τ υ) :=
  (scalarTensorEquiv R S (twistModel σ τ) (twistModel σ υ)).symm.trans
    ((Algebra.TensorProduct.congr (twistRecoveryEquiv σ τ hH)
      (twistRecoveryEquiv σ υ hJ)).trans
        ((scalarTensorEquiv R S H J).trans
          (twistRecoveryEquiv σ (twistAction τ υ) hHJ).symm))

/-- Recovery identifies the explicit comparison with its scalar extension. -/
theorem recoveredTensorEquiv_eq :
    (recoveredTensorEquiv σ τ υ hH hJ hHJ).toAlgHom.restrictScalars R =
      Algebra.TensorProduct.map (AlgHom.id R S) (twistTensorMap σ τ υ) := by
  apply AlgHom.toLinearMap_injective
  ext s x y
  change recoveredTensorEquiv σ τ υ hH hJ hHJ (s ⊗ₜ[R] (x ⊗ₜ[R] y)) =
    s ⊗ₜ[R] twistTensorMap σ τ υ (x ⊗ₜ[R] y)
  apply (twistRecoveryEquiv σ (twistAction τ υ) hHJ).injective
  simp only [recoveredTensorEquiv, AlgEquiv.coe_toAlgHom,
    AlgEquiv.trans_apply, scalarTensorEquiv_symm_tmul,
    Algebra.TensorProduct.congr_apply, twistRecoveryEquiv_tmul, one_smul,
    AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul]
  rw [← TensorProduct.smul_tmul', map_smul, scalarTensorEquiv_product, twistTensorMap_tmul]

include hH hJ hHJ in
/-- The canonical tensor comparison is bijective by faithful flat descent. -/
theorem twistTensorMap_bijective [Module.FaithfullyFlat R S] :
    Function.Bijective (twistTensorMap σ τ υ) := by
  apply bijective_of_scalar_map (S := S)
  rw [← recoveredTensorEquiv_eq σ τ υ hH hJ hHJ]
  exact (recoveredTensorEquiv σ τ υ hH hJ hHJ).bijective

/-- The effective tensor comparison for the actual fixed algebras. -/
def twistTensorEquiv [Module.FaithfullyFlat R S] :
    twistModel σ τ ⊗[R] twistModel σ υ ≃ₐ[R] twistModel σ (twistAction τ υ) :=
  AlgEquiv.ofBijective (twistTensorMap σ τ υ) (twistTensorMap_bijective σ τ υ hH hJ hHJ)

end SemilinearDescent
