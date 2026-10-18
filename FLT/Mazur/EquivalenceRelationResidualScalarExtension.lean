/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationResidualSectionExtension
public import FLT.Mazur.ResidualProductLinearExtension
public import FLT.Mazur.SplitSubmoduleReduction

/-!
# Original residual coefficients stay visible under residue scalar change

The actual residual restriction supplies its scalar algebra. Extension by zero
is a split linear map over any original coefficient scalars. Its range has no
reduction kernel; this statement concerns the residual-supported summand, not
the still-uncontrolled original boundary and correction submodules.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S : Scheme.{0}} (j : S ⟶ source p q I o) [Mono j] [S.IsSeparated]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ σ, (ρ σ).hom ≫ j = j ≫ (action e I o σ).hom)
set_option quotPrecheck false
local notation "O" => residualPermutationOpen e I o j ρ hj
local notation "B" => Γ(SourceRestriction.relation j j, ⊤)
local notation "C" => Γ((O).toScheme, ⊤)
local notation "E" => (residualBranchSectionsIso e I o j ρ hj).commRingCatIsoToRingEquiv
variable (R : Type*) [CommRing R] [Algebra R Γ(SourceRestriction.relation j j, ⊤)]

/-- Scalars on the actual residual ring are pulled back from the entire original relation. -/
@[instance_reducible] def residualCoefficientAlgebra : Algebra R C :=
  ((O).ι.appTop.hom.comp (algebraMap R B)).toAlgebra
attribute [local instance] residualCoefficientAlgebra

/-- The product factor carries the same actual residual scalar algebra. -/
local instance residualBranchCoefficientAlgebra :
    Algebra R Γ((residualBranchOpen e I o j ρ hj none).toScheme, ⊤) :=
  residualCoefficientAlgebra e I o j ρ hj R

/-- The coefficient product projection has the actual original scalar action. -/
theorem residualCoefficient_scalar (r : R) :
    ResidualProductExtension.projection E (algebraMap R B r) = algebraMap R C r :=
  residualBranchSectionsIso_apply e I o j ρ hj (algebraMap R B r) none

/-- The actual residual extension is linear over any original coefficient scalars. -/
def residualSectionLinearExtension : C →ₗ[R] B :=
  ResidualProductExtension.extensionLinear E R (residualCoefficient_scalar e I o j ρ hj R)

/-- The actual residual restriction is linear for the same scalars. -/
def residualSectionLinearRestriction : B →ₗ[R] C :=
  ResidualProductExtension.projectionLinear E R (residualCoefficient_scalar e I o j ρ hj R)

/-- The constructed original coefficient maps form a splitting. -/
theorem residualSectionLinear_split :
    (residualSectionLinearRestriction e I o j ρ hj R).comp
      (residualSectionLinearExtension e I o j ρ hj R) = LinearMap.id :=
  ResidualProductExtension.projectionLinear_comp_extensionLinear E R
    (residualCoefficient_scalar e I o j ρ hj R)

/-- No scalar change, including residue fields, hides actual residual coefficients. -/
theorem residualSection_baseChange_injective (T : Type*) [CommRing T] [Algebra R T] :
    Function.Injective ((residualSectionLinearExtension e I o j ρ hj R).baseChange T) :=
  ResidualProductExtension.baseChange_extension_injective E R
    (residualCoefficient_scalar e I o j ρ hj R) T

/-- Ideal multiples inside the actual residual summand are precisely the ambient ones. -/
theorem residualSection_range_inf_smul (J : Ideal R) :
    LinearMap.range (residualSectionLinearExtension e I o j ρ hj R) ⊓
        J • (⊤ : Submodule R B) =
      J • LinearMap.range (residualSectionLinearExtension e I o j ρ hj R) :=
  SplitSubmoduleReduction.range_inf_smul_top _ _ (residualSectionLinear_split e I o j ρ hj R) J

/-- Reduction of the actual residual summand has no inclusion kernel. -/
theorem residualSection_reduction_injective (J : Ideal R) :
    Function.Injective (SubmoduleReduction.inclusion J
      (LinearMap.range (residualSectionLinearExtension e I o j ρ hj R))) :=
  SplitSubmoduleReduction.reduced_range_injective _ _
    (residualSectionLinear_split e I o j ρ hj R) J

end FLT.Mazur.EquivalenceRelationNormalizedFrames
