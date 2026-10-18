/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedResidualExtension
public import FLT.Mazur.ResidualProductLinearExtension
public import FLT.Mazur.SplitSubmoduleReduction

/-!
# Scalar extension of the independent mixed residual summand

Every original mixed test carries the residual splitting over its original
scalars. It survives arbitrary scalar change and has injective reduction.
The graph-zero condition on an equation map remains explicit.
-/

@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  [(source p q J o').IsSeparated]
  {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')
set_option quotPrecheck false
local notation "O" => mixedResidualTestOpen e o o' z
local notation "B" => Γ(T, ⊤)
local notation "C" => Γ((O).toScheme, ⊤)
local notation "E" => (mixedResidualBranchSectionsIso e o o' z).commRingCatIsoToRingEquiv
variable (R : Type*) [CommRing R] [Algebra R Γ(T, ⊤)]

/-- The actual original restriction defines scalars on the mixed residual ring. -/
@[instance_reducible] def mixedResidualCoefficientAlgebra : Algebra R C :=
  ((O).ι.appTop.hom.comp (algebraMap R B)).toAlgebra
attribute [local instance] mixedResidualCoefficientAlgebra

/-- The product factor carries the same actual residual scalar algebra. -/
local instance mixedResidualBranchCoefficientAlgebra :
    Algebra R Γ((mixedResidualBranchOpen e o o' z none).toScheme, ⊤) :=
  mixedResidualCoefficientAlgebra e o o' z R

/-- Residual scalar restriction is the coordinate of the full original decomposition. -/
theorem mixedResidualCoefficient_scalar (r : R) :
    ResidualProductExtension.projection E (algebraMap R B r) = algebraMap R C r :=
  mixedResidualBranchSectionsIso_apply e o o' z (algebraMap R B r) none

/-- Mixed residual extension by zero over the original scalars. -/
def mixedResidualSectionLinearExtension : C →ₗ[R] B :=
  ResidualProductExtension.extensionLinear E R (mixedResidualCoefficient_scalar e o o' z R)

/-- Mixed residual restriction over those same scalars. -/
def mixedResidualSectionLinearRestriction : B →ₗ[R] C :=
  ResidualProductExtension.projectionLinear E R (mixedResidualCoefficient_scalar e o o' z R)

/-- These actual original maps split. -/
theorem mixedResidualSectionLinear_split :
    (mixedResidualSectionLinearRestriction e o o' z R).comp
      (mixedResidualSectionLinearExtension e o o' z R) = LinearMap.id :=
  ResidualProductExtension.projectionLinear_comp_extensionLinear E R
    (mixedResidualCoefficient_scalar e o o' z R)

/-- Independent mixed residual coefficients remain visible after every scalar change. -/
theorem mixedResidualSection_baseChange_injective
    (S : Type*) [CommRing S] [Algebra R S] :
    Function.Injective ((mixedResidualSectionLinearExtension e o o' z R).baseChange S) :=
  ResidualProductExtension.baseChange_extension_injective E R
    (mixedResidualCoefficient_scalar e o o' z R) S

/-- Reduction has no inclusion kernel on the actual mixed residual summand. -/
theorem mixedResidualSection_reduction_injective (K : Ideal R) :
    Function.Injective (SubmoduleReduction.inclusion K
      (LinearMap.range (mixedResidualSectionLinearExtension e o o' z R))) :=
  SplitSubmoduleReduction.reduced_range_injective _ _
    (mixedResidualSectionLinear_split e o o' z R) K

/-- Once actual graph equations hold, residual equations detect the full scalar correction. -/
theorem mixedResidual_baseChange_equation_iff {M : Type*} [AddCommGroup M] [Module R M]
    (F : M →ₗ[R] B)
    (hF : ∀ x (ι : J ↪ I), (mixedEmbeddingTestOpen e o o' z ι).ι.appTop (F x) = 0)
    (S : Type*) [CommRing S] [Algebra R S] (x : S ⊗[R] M) (c : S ⊗[R] C) :
    F.baseChange S x = (mixedResidualSectionLinearExtension e o o' z R).baseChange S c ↔
      ((mixedResidualSectionLinearRestriction e o o' z R).comp F).baseChange S x = c := by
  apply ResidualProductExtension.baseChange_equation_iff E R
    (mixedResidualCoefficient_scalar e o o' z R) F
  intro y ι
  exact (mixedResidualBranchSectionsIso_apply e o o' z (F y) (some ι)).trans (hF y ι)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
