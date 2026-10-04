/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalComponentQuotientEtale
public import FLT.GroupScheme.IntegralSubquotientExtension

/-! # The original connected–étale extension at each finite-flat level -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.FF
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))

/-- The original quotient is surjective on geometric generic points. -/
theorem rationalComponentProjection_points_surjective :
    Function.Surjective (genericHom X.rationalComponentProjection) := by
  rw [X.rationalComponentProjection_genericHom]
  exact X.rationalComponentGenericProjection_surjective

/-- The original generic point sequence is exact, with its original maps. -/
theorem rationalComponentProjection_points_exact (x : X.Points) :
    genericHom X.rationalComponentProjection x = 0 ↔
      ∃ a, genericHom X.rationalIdentityComponentInclusion a = x := by
  rw [X.rationalComponentProjection_genericHom]
  exact X.rationalComponentGenericProjection_exact x

/-- The original finite-flat model is an extension of its actual étale quotient
by its actual connected component. No splitting or section is asserted. -/
def rationalConnectedEtaleExtension :
    ModelExtension X.rationalIdentityComponent X X.rationalComponentQuotient where
  inclusion := X.rationalIdentityComponentInclusion
  quotient := X.rationalComponentProjection
  compositionZero := by
    have h : X.rationalIdentityComponentInclusion.comp X.rationalComponentProjection =
        ModelHom.zero X.rationalIdentityComponent X.rationalComponentQuotient := by
      apply genericHom_injective
      ext a
      simp only [genericHom_comp, ModelHom.genericHom_zero]
      exact (X.rationalComponentProjection_points_exact _).mpr ⟨a, rfl⟩
    exact congrArg BialgHom.toAlgHom h
  pointsInjective := X.rationalIdentityComponentInclusion_genericHom_injective
  pointsSurjective := X.rationalComponentProjection_points_surjective
  pointsExact := X.rationalComponentProjection_points_exact
  quotientFaithfullyFlat := X.rationalComponentProjection_faithfullyFlat
  torsorEquiv := by
    let : Algebra X.rationalComponentQuotient.CoordinateRing X.CoordinateRing :=
      X.rationalComponentProjection.toAlgHom.toRingHom.toAlgebra
    let : IsScalarTower O X.rationalComponentQuotient.CoordinateRing X.CoordinateRing :=
      IsScalarTower.of_algebraMap_eq' X.rationalComponentProjection.toAlgHom.comp_algebraMap.symm
    exact HopfAlgebra.torsorEquivOfIdealEq X.rationalComponentProjection
      (by ext; rfl) X.rationalIdentityComponentIdeal X.rationalComponentProjection_kernel
  torsorEquivSecond := by
    let : Algebra X.rationalComponentQuotient.CoordinateRing X.CoordinateRing :=
      X.rationalComponentProjection.toAlgHom.toRingHom.toAlgebra
    let : IsScalarTower O X.rationalComponentQuotient.CoordinateRing X.CoordinateRing :=
      IsScalarTower.of_algebraMap_eq' X.rationalComponentProjection.toAlgHom.comp_algebraMap.symm
    exact HopfAlgebra.torsorEquivOfIdealEqSecond X.rationalComponentProjection
      (by ext; rfl) X.rationalIdentityComponentIdeal X.rationalComponentProjection_kernel
end ThreeAdicPlan.FF
