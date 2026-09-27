/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistTensor
public import Mathlib.RingTheory.Etale.Descent

/-!
# Etale generic fibres of quadratic twists

Scalar recovery and faithfully flat descent transfer etaleness of the generic
fibre from an algebra to its quadratic fixed model.
-/

@[expose] public section

open scoped TensorProduct

namespace QuadraticTwist

universe v
variable {R H : Type v} [CommRing R] [CommRing H] [Algebra R H]
variable (u : Rˣ) (ι : H ≃ₐ[R] H) (hι : Function.Involutive ι)
variable (r : R) (hr : 2 * r = 1)

/-- Scalar recovery remains an equivalence over any algebra over the quadratic coefficients. -/
noncomputable def scalarExtensionEquivTower (T : Type v) [CommRing T]
    [Algebra R T] [Algebra (QuadraticAlgebra R (u : R) 0) T]
    [IsScalarTower R (QuadraticAlgebra R (u : R) 0) T] :
    T ⊗[R] model (u : R) ι ≃ₐ[T] T ⊗[R] H :=
  (Algebra.TensorProduct.cancelBaseChange R (QuadraticAlgebra R (u : R) 0) T T
    (model (u : R) ι)).symm.trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl
      (scalarExtensionEquivOver u ι hι r hr)).trans
      (Algebra.TensorProduct.cancelBaseChange R (QuadraticAlgebra R (u : R) 0) T T H))

include hι hr in
/-- Etaleness after scalar extension descends to the quadratic fixed model. -/
theorem model_baseChange_etale [Nontrivial R] (K : Type v) [Field K] [Algebra R K]
    [Algebra.Etale K (K ⊗[R] H)] :
    Algebra.Etale K (K ⊗[R] model (u : R) ι) := by
  let S := QuadraticAlgebra R (u : R) 0
  let T := K ⊗[R] S
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R S T := Algebra.TensorProduct.right_isScalarTower
  let e : T ⊗[K] (K ⊗[R] model (u : R) ι) ≃ₐ[T] T ⊗[K] (K ⊗[R] H) :=
    (Algebra.TensorProduct.cancelBaseChange R K T T (model (u : R) ι)).trans
      ((scalarExtensionEquivTower u ι hι r hr T).trans
        (Algebra.TensorProduct.cancelBaseChange R K T T H).symm)
  let : Algebra.Etale T (T ⊗[K] (K ⊗[R] model (u : R) ι)) :=
    Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat T

end QuadraticTwist
