/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalConnectedKernel
public import FLT.GroupScheme.IntegralKernelEquations
public import FLT.GroupScheme.IntegralQuotientFaithfullyFlat
public import FLT.GroupScheme.RaynaudOrderNineExtension

/-! # The original finite-flat quotient by the connected identity component

The quotient is constructed by contraction from the actual generic quotient.
The quotient map, faithful flatness and integral kernel ideal are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.FF
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
variable (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))

/-- A finite-flat witness for the actual generic quotient group exists. -/
theorem exists_rationalComponentQuotient : ∃ Q : FF O K, ∃ q : GenericGaloisHom X Q,
    Function.Surjective q ∧
      (∀ x, q x = 0 ↔ ∃ a, genericHom X.rationalIdentityComponentInclusion a = x) ∧
      Nat.card Q.Points =
        (genericHom X.rationalIdentityComponentInclusion).toAddMonoidHom.range.index :=
  (genericHom X.rationalIdentityComponentInclusion).exists_exact_quotient

/-- A generic quotient witness used only to construct the contracted integral quotient. -/
def rationalComponentQuotientWitness : FF O K := X.exists_rationalComponentQuotient.choose

/-- The original generic projection to that witness. -/
def rationalComponentGenericProjection : GenericGaloisHom X X.rationalComponentQuotientWitness :=
  X.exists_rationalComponentQuotient.choose_spec.choose

/-- The selected generic projection is surjective by its construction. -/
theorem rationalComponentGenericProjection_surjective :
    Function.Surjective X.rationalComponentGenericProjection :=
  X.exists_rationalComponentQuotient.choose_spec.choose_spec.1

/-- The generic projection has precisely the actual connected generic subgroup as kernel. -/
theorem rationalComponentGenericProjection_exact (x : X.Points) :
    X.rationalComponentGenericProjection x = 0 ↔
      ∃ a, genericHom X.rationalIdentityComponentInclusion a = x :=
  X.exists_rationalComponentQuotient.choose_spec.choose_spec.2.1 x

/-- The quotient by the actual connected subgroup, contracted inside the original coordinates. -/
def rationalComponentQuotient : FF O K :=
  X.rationalComponentGenericProjection.flatQuotient X.rationalComponentGenericProjection_surjective

/-- The original integral quotient morphism. -/
def rationalComponentProjection : ModelHom X X.rationalComponentQuotient :=
  X.rationalComponentGenericProjection.toFlatQuotient
    X.rationalComponentGenericProjection_surjective

/-- The integral quotient retains the chosen actual generic projection. -/
theorem rationalComponentProjection_genericHom :
    genericHom X.rationalComponentProjection = X.rationalComponentGenericProjection := by
  ext x
  exact X.rationalComponentGenericProjection.genericHom_toFlatQuotient _ x

/-- The component quotient is faithfully flat over its actual integral coordinate algebra. -/
theorem rationalComponentProjection_faithfullyFlat :
    X.rationalComponentProjection.toAlgHom.toRingHom.FaithfullyFlat :=
  X.rationalComponentGenericProjection.quotientCoordinatesFaithfullyFlat

/-- The kernel of the original quotient is exactly the original connected component. -/
theorem rationalComponentProjection_kernel :
    HopfAlgebra.augmentationIdeal X.rationalComponentProjection =
      X.rationalIdentityComponentIdeal := by
  have h := (genericHom X.rationalIdentityComponentInclusion).quotientKernelIdealEqClosureIdeal
    X.rationalComponentGenericProjection
    X.rationalComponentGenericProjection_surjective X.rationalComponentGenericProjection_exact
  rw [← X.rationalIdentityComponentInclusion.ker_eq_closureIdeal
    X.rationalIdentityComponentInclusion_genericHom_injective
    X.rationalIdentityComponentInclusion_surjective,
    X.rationalIdentityComponentInclusion_ker] at h
  exact h
end ThreeAdicPlan.FF
