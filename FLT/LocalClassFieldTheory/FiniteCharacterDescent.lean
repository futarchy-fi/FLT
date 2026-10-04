/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisTowerCochainDescent
public import FLT.LocalClassFieldTheory.IntegralCochainCup

/-!
# Descent of a discrete character to its finite fixed field

The open kernel determines the field. Restriction has exactly that kernel,
so the descended character is faithful, with no factorization premise.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {A : Type} [Group A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : Gal(L/K) →ₜ* A)

/-- The open normal subgroup cut out by a discrete continuous character. -/
def characterOpenKernel : OpenNormalSubgroup Gal(L/K) where
  toSubgroup := χ.toMonoidHom.ker
  isOpen' := χ.continuous.isOpen_preimage {1} (isOpen_discrete _)
  isNormal' := inferInstance

/-- The actual fixed field of the character kernel. -/
def characterFixedField : IntermediateField K L :=
  IntermediateField.fixedField (characterOpenKernel K L χ).toSubgroup

/-- Openness of the character kernel makes its fixed field finite. -/
instance characterFixedFieldFinite : FiniteDimensional K (characterFixedField K L χ) :=
  galoisOpenStage_fixedField_finite K L (characterOpenKernel K L χ)

/-- Normality of the character kernel makes its fixed field Galois. -/
instance characterFixedFieldGalois : IsGalois K (characterFixedField K L χ) := by
  unfold characterFixedField
  infer_instance

/-- Restriction to the character field has precisely the character kernel. -/
theorem characterFixedField_kernel :
    (AlgEquiv.restrictNormalHom (characterFixedField K L χ) :
      Gal(L/K) →* Gal(characterFixedField K L χ/K)).ker = χ.toMonoidHom.ker :=
  galoisStage_restriction_ker K L (characterOpenKernel K L χ)

/-- The original character descends along actual restriction of automorphisms. -/
def descendedFiniteCharacter : Gal(characterFixedField K L χ/K) →* A :=
  (AlgEquiv.restrictNormalHom (characterFixedField K L χ)).liftOfSurjective
    (AlgEquiv.restrictNormalHom_surjective L)
    ⟨χ.toMonoidHom, le_of_eq (characterFixedField_kernel K L χ)⟩

/-- Evaluation after restriction recovers the original character. -/
theorem descendedFiniteCharacter_restrict (g : Gal(L/K)) :
    descendedFiniteCharacter K L χ
      (AlgEquiv.restrictNormalHom (characterFixedField K L χ) g) = χ g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

/-- The descended character is faithful because its field uses the exact kernel. -/
theorem descendedFiniteCharacter_injective :
    Function.Injective (descendedFiniteCharacter K L χ) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L g
  rw [descendedFiniteCharacter_restrict] at hg
  change s ∈ (AlgEquiv.restrictNormalHom (characterFixedField K L χ) :
    Gal(L/K) →* Gal(characterFixedField K L χ/K)).ker
  rw [characterFixedField_kernel]
  exact hg

end LocalClassFieldTheory
