/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ActualThreeAdicKummerCube
public import FLT.GroupScheme.ConstantMuThreeCocycleSplitting
public import FLT.GroupScheme.ConstantMuThreeKummerValuations
public import FLT.GroupScheme.SupportedKummerValuations

/-!
# Splitting actual constant-three extensions of the cube-root group

The extension's own finite Galois cocycle supplies a rational Kummer parameter.
Its finite-flat model forces valuation divisibility away from two and three,
and the actual three-adic section makes the parameter a cube over `ℚ₃`.
The numerical local-global criterion makes it a rational cube. The resulting
coboundary constructs a generic splitting with the prescribed maps, and the
integral extension theorem lifts those maps over `ℤ[1/2]`.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan.FiniteFlatExtension

variable {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree)

/-- The actual extension admits a rational generic splitting with exactly its
prescribed inclusion and quotient, with no supplied splitting or Kummer data. -/
theorem exists_constantThree_muThree_genericSplitSequence :
    ∃ s : GenericSplitSequence constantThree.toFF X.toFF muThree.toFF,
      genericHom (X := constantThree.toFF) (Y := X.toFF) E.inclusion = s.inclusion ∧
      genericHom (X := X.toFF) (Y := muThree.toFF) E.quotient = s.projection := by
  obtain ⟨a, b, ha, hb, hpow, heq⟩ := E.exists_actual_cubic_kummer_parameter
  have hlocal := E.actual_cubic_kummer_parameter_three_adic_cube a b hpow heq
  have hcube := rational_cube_of_away_valuations_and_three_adic_cube a ha
    (E.actual_cubic_kummer_parameter_away_valuations a ha b hpow) hlocal
  exact E.exists_genericSplitSequence_of_parameter_cube a b hb hpow heq hcube

/-- A chosen generic splitting of the actual extension, constructed from its
finite-flat model and its prescribed maps. -/
def constantThreeMuThreeGenericSplitting :
    GenericSplitSequence constantThree.toFF X.toFF muThree.toFF :=
  E.exists_constantThree_muThree_genericSplitSequence.choose

/-- The generic splitting's inclusion is the original integral inclusion on points. -/
theorem constantThreeMuThreeGenericSplitting_inclusion :
    genericHom (X := constantThree.toFF) (Y := X.toFF) E.inclusion =
      E.constantThreeMuThreeGenericSplitting.inclusion :=
  E.exists_constantThree_muThree_genericSplitSequence.choose_spec.1

/-- The generic splitting's projection is the original integral quotient on points. -/
theorem constantThreeMuThreeGenericSplitting_projection :
    genericHom (X := X.toFF) (Y := muThree.toFF) E.quotient =
      E.constantThreeMuThreeGenericSplitting.projection :=
  E.exists_constantThree_muThree_genericSplitSequence.choose_spec.2

/-- The actual extension has an integral splitting over `ℤ[1/2]`; it uniquely
lifts the constructed rational splitting. -/
theorem existsUnique_constantThree_muThree_actual_modelSplitting :
    ∃! sO : ModelSplitting (S := constantThree.toFF) (X := X.toFF) (Q := muThree.toFF)
        E.inclusion E.quotient,
      sO.toGenericSplitSequence = E.constantThreeMuThreeGenericSplitting :=
  E.existsUnique_constantThree_muThree_modelSplitting E.constantThreeMuThreeGenericSplitting
    E.constantThreeMuThreeGenericSplitting_inclusion
    E.constantThreeMuThreeGenericSplitting_projection

/-- An integral splitting of the actual prescribed extension. -/
def constantThreeMuThreeModelSplitting :
    ModelSplitting (S := constantThree.toFF) (X := X.toFF) (Q := muThree.toFF)
      E.inclusion E.quotient :=
  E.existsUnique_constantThree_muThree_actual_modelSplitting.exists.choose

end ThreeAdicPlan.FiniteFlatExtension
