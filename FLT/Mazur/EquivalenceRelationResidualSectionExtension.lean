/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationResidualBranchDecomposition
public import FLT.Mazur.ResidualProductExtension

/-!
# Extending actual residual coefficients to the whole original relation

Residual coefficients extend by zero on permutation branches. The discrepancy
of a moving invariant is exactly this extension of its residual discrepancy.
Thus no original equation or nilpotent coefficient is lost in the residual target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S : Scheme.{0}} (j : S ⟶ source p q I o) [Mono j] [S.IsSeparated]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ σ, (ρ σ).hom ≫ j = j ≫ (action e I o σ).hom)
local notation "O" => residualPermutationOpen e I o j ρ hj
set_option quotPrecheck false
local notation "E" => (residualBranchSectionsIso e I o j ρ hj).commRingCatIsoToRingEquiv

/-- Extension by zero uses the actual original residual and permutation decomposition. -/
def residualSectionExtension : Γ((O).toScheme, ⊤) →+ Γ(relation j j, ⊤) :=
  ResidualProductExtension.extension E

/-- Every residual coefficient extends with its exact restriction unchanged. -/
theorem residualSectionExtension_restrict (c : Γ((O).toScheme, ⊤)) :
    (O).ι.appTop (residualSectionExtension e I o j ρ hj c) = c := by
  exact (residualBranchSectionsIso_apply e I o j ρ hj _ none).symm.trans
    (ResidualProductExtension.extension_none E c)

/-- The extension vanishes on every original permutation branch. -/
theorem residualSectionExtension_permutation (c : Γ((O).toScheme, ⊤)) (σ : Equiv.Perm I) :
    (permutationTestOpen e I o (original j j) σ).ι.appTop
      (residualSectionExtension e I o j ρ hj c) = 0 := by
  exact (residualBranchSectionsIso_apply e I o j ρ hj _ (some σ)).symm.trans
    (ResidualProductExtension.extension_some E c σ)

/-- No coefficient is lost when it is extended to the entire original relation. -/
theorem residualSectionExtension_injective :
    Function.Injective (residualSectionExtension e I o j ρ hj) :=
  ResidualProductExtension.extension_injective E

/-- Original multiplication acts through actual residual restriction. -/
theorem residualSectionExtension_mul (a : Γ(relation j j, ⊤))
    (c : Γ((O).toScheme, ⊤)) :
    a * residualSectionExtension e I o j ρ hj c =
      residualSectionExtension e I o j ρ hj ((O).ι.appTop a * c) := by
  apply residualPermutation_sections_ext e I o j ρ hj
  · simp only [map_mul, residualSectionExtension_restrict]
  · intro σ
    simp only [map_mul, residualSectionExtension_permutation, mul_zero]

/-- A moving-invariant discrepancy is reconstructed exactly from the residual equations. -/
theorem invariant_discrepancy_residualExtension (t : invariantCoordinates ρ) :
    residualSectionExtension e I o j ρ hj
      ((O).ι.appTop ((SourceRestriction.fst j j).appTop t.val -
        (SourceRestriction.snd j j).appTop t.val)) =
      (SourceRestriction.fst j j).appTop t.val -
        (SourceRestriction.snd j j).appTop t.val := by
  apply residualPermutation_sections_ext e I o j ρ hj
  · exact residualSectionExtension_restrict e I o j ρ hj _
  · intro σ
    rw [residualSectionExtension_permutation, map_sub]
    symm
    exact sub_eq_zero.mpr (permutationPiece_invariant_equalizes e I o j ρ hj t σ)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
