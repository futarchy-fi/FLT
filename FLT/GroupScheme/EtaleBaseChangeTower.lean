/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatFiltration
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Étaleness of base-changed finite-flat extensions

If the kernel is étale over the original base, the quotient morphism is étale.
It is then enough for the quotient group to become étale after scalar extension
in order for the middle group to become étale as well.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped TensorProduct

namespace Algebra

/-- Base change of a tower with étale upper map is étale when the base-changed
lower algebra is étale. -/
theorem etale_tensorProduct_of_tower (R A B S : Type)
    [CommRing R] [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R S] [Etale A B] [Etale S (S ⊗[R] A)] : Etale S (S ⊗[R] B) := by
  let P := A ⊗[R] S
  let : Algebra S P := TensorProduct.rightAlgebra
  let c : S ⊗[R] A ≃ₐ[S] P :=
    { (TensorProduct.comm R S A).toRingEquiv with
      commutes' := fun s ↦ by
        change (TensorProduct.comm R S A) (s ⊗ₜ[R] (1 : A)) = 1 ⊗ₜ[R] s
        simp }
  let : Etale S P := Etale.of_equiv c
  let T := P ⊗[A] B
  let : Algebra S T := Algebra.compHom T (algebraMap S P)
  let : IsScalarTower S P T := IsScalarTower.of_algebraMap_eq' rfl
  let : Etale P T := Etale.baseChange A B P
  let : Etale S T := Etale.comp S P T
  let e : T ≃+* S ⊗[R] B :=
    (TensorProduct.comm A P B).toRingEquiv.trans
      ((TensorProduct.cancelBaseChange R A B B S).toRingEquiv.trans
        (TensorProduct.comm R B S).toRingEquiv)
  let eS : T ≃ₐ[S] S ⊗[R] B :=
    { e with
      commutes' := by
        intro s
        change e ((1 ⊗ₜ[R] s) ⊗ₜ[A] (1 : B)) = s ⊗ₜ[R] (1 : B)
        change s ⊗ₜ[R] ((1 : A) • (1 : B)) = s ⊗ₜ[R] (1 : B)
        rw [one_smul] }
  exact Etale.of_equiv eS

end Algebra

namespace ThreeAdicPlan.FiniteFlatExtension

variable {R : Type} [CommRing R] [Algebra R ℚ]
    {A X Q : FiniteFlatObject R} (E : FiniteFlatExtension A X Q)

/-- An extension with étale kernel has an étale prescribed quotient morphism. -/
theorem quotient_etale [Algebra.Etale R A.model.CoordinateRing] :
    letI := E.quotient.toAlgHom.toRingHom.toAlgebra
    Algebra.Etale Q.model.CoordinateRing X.model.CoordinateRing := by
  let : Algebra Q.model.CoordinateRing X.model.CoordinateRing :=
    E.quotient.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R Q.model.CoordinateRing X.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.quotient.toAlgHom.comp_algebraMap.symm
  let : Module.FaithfullyFlat Q.model.CoordinateRing X.model.CoordinateRing :=
    E.quotientFaithfullyFlat
  let : Algebra.Etale X.model.CoordinateRing
      (X.model.CoordinateRing ⊗[Q.model.CoordinateRing] X.model.CoordinateRing) :=
    Algebra.Etale.of_equiv E.torsorEquiv.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat X.model.CoordinateRing

include E in
/-- Away étaleness of the actual quotient implies away étaleness of the actual
middle model when the original kernel is étale. -/
theorem etale_scalarExtension (S : Type) [CommRing S] [Algebra R S]
    [Algebra.Etale R A.model.CoordinateRing]
    [Algebra.Etale S (S ⊗[R] Q.model.CoordinateRing)] :
    Algebra.Etale S (S ⊗[R] X.model.CoordinateRing) := by
  let : Algebra Q.model.CoordinateRing X.model.CoordinateRing :=
    E.quotient.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R Q.model.CoordinateRing X.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.quotient.toAlgHom.comp_algebraMap.symm
  let := E.quotient_etale
  exact Algebra.etale_tensorProduct_of_tower R Q.model.CoordinateRing X.model.CoordinateRing S

end ThreeAdicPlan.FiniteFlatExtension
