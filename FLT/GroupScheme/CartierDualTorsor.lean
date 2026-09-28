/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualAugmentation

/-!
# The integral torsor comparison for a Cartier-dual extension

The canonical Hopf torsor equivalence, followed by the augmentation quotient
identification, gives the required comparison with the Cartier dual of the
original quotient. Its second coordinate is the given dual Hopf coaction.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.FiniteFlatExtension

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]
  {A H Q : FiniteFlatObject R}

/-- The canonical integral torsor comparison of the reversed dual extension. -/
def dualTorsorEquiv (E : FiniteFlatExtension A H Q) :
    letI := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
    H.cartierDual.model.CoordinateRing ⊗[A.cartierDual.model.CoordinateRing]
      H.cartierDual.model.CoordinateRing ≃ₐ[H.cartierDual.model.CoordinateRing]
        H.cartierDual.model.CoordinateRing ⊗[R] Q.cartierDual.model.CoordinateRing := by
  let := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R A.cartierDual.model.CoordinateRing
      H.cartierDual.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.inclusion.cartierDual.toAlgHom.comp_algebraMap.symm
  exact (HopfAlgebra.torsorEquiv E.inclusion.cartierDual rfl).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : H.cartierDual.model.CoordinateRing ≃ₐ[
      H.cartierDual.model.CoordinateRing] H.cartierDual.model.CoordinateRing) E.dualKernelEquiv)

/-- The dual torsor comparison uses comultiplication and the transposed original quotient. -/
theorem dualTorsorEquivSecond (E : FiniteFlatExtension A H Q) :
    letI := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
    ∀ φ : H.cartierDual.model.CoordinateRing,
      E.dualTorsorEquiv (1 ⊗ₜ[A.cartierDual.model.CoordinateRing] φ) =
        Algebra.TensorProduct.map (AlgHom.id R H.cartierDual.model.CoordinateRing)
          E.quotient.cartierDual.toAlgHom (Coalgebra.comul (R := R) φ) := by
  let := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R A.cartierDual.model.CoordinateRing
      H.cartierDual.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.inclusion.cartierDual.toAlgHom.comp_algebraMap.symm
  intro φ
  change (Algebra.TensorProduct.congr (AlgEquiv.refl : H.cartierDual.model.CoordinateRing ≃ₐ[
      H.cartierDual.model.CoordinateRing] H.cartierDual.model.CoordinateRing) E.dualKernelEquiv)
    (HopfAlgebra.torsorHom E.inclusion.cartierDual rfl (1 ⊗ₜ[_] φ)) = _
  simp only [HopfAlgebra.torsorHom, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  change Algebra.TensorProduct.map (AlgHom.id R H.cartierDual.model.CoordinateRing)
    E.dualKernelEquiv.toAlgHom
      (Algebra.TensorProduct.map (AlgHom.id R H.cartierDual.model.CoordinateRing)
        (Ideal.Quotient.mkₐ R (HopfAlgebra.augmentationIdeal E.inclusion.cartierDual))
          (Coalgebra.comul φ)) = _
  generalize Coalgebra.comul (R := R) φ = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Extensions whose two Cartier-dual end terms are étale have étale Cartier dual. -/
theorem cartierDual_etale (E : FiniteFlatExtension A H Q)
    [Algebra.Etale R A.cartierDual.model.CoordinateRing]
    [Algebra.Etale R Q.cartierDual.model.CoordinateRing] :
    Algebra.Etale R H.cartierDual.model.CoordinateRing := by
  let := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R A.cartierDual.model.CoordinateRing
      H.cartierDual.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.inclusion.cartierDual.toAlgHom.comp_algebraMap.symm
  let := E.dualQuotientFaithfullyFlat
  let : Algebra.Etale H.cartierDual.model.CoordinateRing
      (H.cartierDual.model.CoordinateRing ⊗[A.cartierDual.model.CoordinateRing]
        H.cartierDual.model.CoordinateRing) := Algebra.Etale.of_equiv E.dualTorsorEquiv.symm
  let : Algebra.Etale A.cartierDual.model.CoordinateRing H.cartierDual.model.CoordinateRing :=
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat H.cartierDual.model.CoordinateRing
  exact Algebra.Etale.comp R A.cartierDual.model.CoordinateRing H.cartierDual.model.CoordinateRing

end ThreeAdicPlan.FiniteFlatExtension
