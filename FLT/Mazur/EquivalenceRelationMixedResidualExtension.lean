/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedResidualDecomposition
public import FLT.Mazur.ResidualProductExtension

/-!
# Extension by zero on independent mixed original frames

The unchanged mixed residual component is a split coefficient summand on every
original test. Reconstruction requires zero on each actual embedding branch;
no equality of frame sizes or identification of independent labels is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  [(source p q J o').IsSeparated]
  {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')
local notation "O" => mixedResidualTestOpen e o o' z
set_option quotPrecheck false
local notation "E" => (mixedResidualBranchSectionsIso e o o' z).commRingCatIsoToRingEquiv

/-- Extend a mixed residual coefficient by zero on every original embedding graph. -/
def mixedResidualSectionExtension : Γ((O).toScheme, ⊤) →+ Γ(T, ⊤) :=
  ResidualProductExtension.extension E

/-- Actual restriction retracts the mixed extension. -/
theorem mixedResidualSectionExtension_restrict (c : Γ((O).toScheme, ⊤)) :
    (O).ι.appTop (mixedResidualSectionExtension e o o' z c) = c := by
  exact (mixedResidualBranchSectionsIso_apply e o o' z _ none).symm.trans
    (ResidualProductExtension.extension_none E c)

/-- Extension is zero on each individually labelled original embedding branch. -/
theorem mixedResidualSectionExtension_embedding (c : Γ((O).toScheme, ⊤)) (ι : J ↪ I) :
    (mixedEmbeddingTestOpen e o o' z ι).ι.appTop
      (mixedResidualSectionExtension e o o' z c) = 0 := by
  exact (mixedResidualBranchSectionsIso_apply e o o' z _ (some ι)).symm.trans
    (ResidualProductExtension.extension_some E c ι)

/-- The full mixed coefficient ring retains every residual coefficient, including nilpotents. -/
theorem mixedResidualSectionExtension_injective :
    Function.Injective (mixedResidualSectionExtension e o o' z) :=
  ResidualProductExtension.extension_injective E

/-- Original multiplication commutes with mixed extension through actual restriction. -/
theorem mixedResidualSectionExtension_mul (a : Γ(T, ⊤)) (c : Γ((O).toScheme, ⊤)) :
    a * mixedResidualSectionExtension e o o' z c =
      mixedResidualSectionExtension e o o' z ((O).ι.appTop a * c) := by
  apply (mixedResidualBranch_sections_eq_iff e o o' z _ _).mpr
  intro i
  cases i with
  | none =>
    change (O).ι.appTop _ = (O).ι.appTop _
    simp only [map_mul, mixedResidualSectionExtension_restrict]
  | some ι =>
    change (mixedEmbeddingTestOpen e o o' z ι).ι.appTop _ =
      (mixedEmbeddingTestOpen e o o' z ι).ι.appTop _
    simp only [map_mul, mixedResidualSectionExtension_embedding, mul_zero]

/-- Every original mixed coefficient zero on embedding branches is reconstructed exactly. -/
theorem mixedResidualSectionExtension_reconstruct (a : Γ(T, ⊤))
    (ha : ∀ ι : J ↪ I, (mixedEmbeddingTestOpen e o o' z ι).ι.appTop a = 0) :
    mixedResidualSectionExtension e o o' z ((O).ι.appTop a) = a := by
  apply (mixedResidualBranch_sections_eq_iff e o o' z _ _).mpr
  intro i
  cases i with
  | none => exact mixedResidualSectionExtension_restrict e o o' z _
  | some ι => exact (mixedResidualSectionExtension_embedding e o o' z _ ι).trans (ha ι).symm

/-- Once graph equations hold, a prescribed mixed residual value fixes the full coefficient. -/
theorem mixedResidualSectionExtension_eq_iff (a : Γ(T, ⊤))
    (ha : ∀ ι : J ↪ I, (mixedEmbeddingTestOpen e o o' z ι).ι.appTop a = 0)
    (c : Γ((O).toScheme, ⊤)) :
    a = mixedResidualSectionExtension e o o' z c ↔ (O).ι.appTop a = c := by
  rw [← mixedResidualSectionExtension_reconstruct e o o' z a ha]
  rw [mixedResidualSectionExtension_restrict]
  exact (mixedResidualSectionExtension_injective e o o' z).eq_iff

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
