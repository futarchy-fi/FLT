/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeFixedGroup
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizationNaturality

/-!
# Odd normalization fixes every auxiliary family with normalized frame

Equality transport fixes every section of the actual family. The original
faithful representation then identifies the entire auxiliary scheme morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelThree.left)
  (hn : SatisfiesNormalization f.appTop.hom)

include hn

/-- Every universal value is unchanged by normalization over an already normalized frame. -/
theorem auxiliarySchemeNormalizedValue_fixed (s : T ⟶ universalGroup.left)
    (hs : s ≫ universalGroup.hom = f ≫ levelThree.hom) :
    auxiliarySchemeNormalizedValue f s hs = s := by
  rw [auxiliarySchemeNormalizedValue,
    auxiliarySchemeNormalizationGroupIso_fixed_inv_fst f hn]
  exact pullback.lift_fst _ _ _

/-- The complete original auxiliary point is fixed on every normalized source scheme. -/
theorem auxiliarySchemeNormalizedPoint_fixed : auxiliarySchemeNormalizedPoint f = f := by
  apply auxiliarySchemePoint_ext _ _ (auxiliarySchemeNormalizedBase_fixed f hn)
  intro a
  rw [auxiliarySchemeNormalizedPoint_value_normalize]
  exact auxiliarySchemeNormalizedValue_fixed f hn _ _

end FLT.Mazur.OddWeierstrassParameter
