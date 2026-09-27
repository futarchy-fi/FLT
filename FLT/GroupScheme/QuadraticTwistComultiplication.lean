/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistMonoidal

/-!
# Comultiplication on a quadratic twist

For a commutative, cocommutative Hopf algebra, inversion commutes with
comultiplication. Tensor compatibility of the fixed algebras therefore
descends comultiplication to the integral twist.
-/

@[expose] public section

open scoped TensorProduct

namespace HopfAlgebra

universe v
variable (R H : Type v) [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Coalgebra.IsCocomm R H]

/-- On a cocommutative Hopf algebra inversion commutes with comultiplication. -/
theorem comul_antipode_equivariant (x : H) :
    Algebra.TensorProduct.congr (antipodeAlgEquiv R H) (antipodeAlgEquiv R H)
        (Bialgebra.comulAlgHom R H x) =
      Bialgebra.comulAlgHom R H (antipodeAlgEquiv R H x) := by
  exact LinearMap.congr_fun (BialgHom.antipode_comp (Bialgebra.comulBialgHom R H)) x

end HopfAlgebra

namespace QuadraticTwist

universe v
variable {R H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Coalgebra.IsCocomm R H]
variable (u : Rˣ) (r : R) (hr : 2 * r = 1)

/-- Comultiplication of the inversion twist, with values in its own tensor square. -/
noncomputable def comul :
    model (u : R) (HopfAlgebra.antipodeAlgEquiv R H) →ₐ[R]
      model (u : R) (HopfAlgebra.antipodeAlgEquiv R H) ⊗[R]
        model (u : R) (HopfAlgebra.antipodeAlgEquiv R H) :=
  (modelTensorEquiv (HopfAlgebra.antipodeAlgEquiv R H) (HopfAlgebra.antipodeAlgEquiv R H)
    u (HopfAlgebra.antipode_involutive R H)
      (HopfAlgebra.antipode_involutive R H) r hr).symm.toAlgHom.comp
    (map (u : R) (HopfAlgebra.antipodeAlgEquiv R H)
      (Algebra.TensorProduct.congr (HopfAlgebra.antipodeAlgEquiv R H)
        (HopfAlgebra.antipodeAlgEquiv R H))
      (Bialgebra.comulAlgHom R H) (HopfAlgebra.comul_antipode_equivariant R H))

/-- The descended comultiplication agrees with the original after tensor comparison. -/
theorem comul_compat (a : model (u : R) (HopfAlgebra.antipodeAlgEquiv R H)) :
    (modelTensorEquiv (HopfAlgebra.antipodeAlgEquiv R H) (HopfAlgebra.antipodeAlgEquiv R H)
        u (HopfAlgebra.antipode_involutive R H) (HopfAlgebra.antipode_involutive R H) r hr
        (comul u r hr a) : QuadraticAlgebra R (u : R) 0 ⊗[R] (H ⊗[R] H)) =
      Algebra.TensorProduct.map (AlgHom.id R _) (Bialgebra.comulAlgHom R H) a.val := by
  exact congrArg Subtype.val
    ((modelTensorEquiv (HopfAlgebra.antipodeAlgEquiv R H) (HopfAlgebra.antipodeAlgEquiv R H)
      u (HopfAlgebra.antipode_involutive R H)
        (HopfAlgebra.antipode_involutive R H) r hr).apply_symm_apply
        (map (u : R) (HopfAlgebra.antipodeAlgEquiv R H)
          (Algebra.TensorProduct.congr (HopfAlgebra.antipodeAlgEquiv R H)
            (HopfAlgebra.antipodeAlgEquiv R H))
          (Bialgebra.comulAlgHom R H) (HopfAlgebra.comul_antipode_equivariant R H) a))

end QuadraticTwist
