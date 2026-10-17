/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizationFixed
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationNaturality

/-!
# Full cyclic normalization fixes every normalized auxiliary frame

The same equality comparison fixes all cyclic values, without distinctness
or coprimality assumptions. Together with the auxiliary point this determines
the original unrestricted cyclic parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Every full cyclic point is fixed when its auxiliary frame is already normalized. -/
theorem cyclicHomNormalizedPoint_fixed (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hn : SatisfiesNormalization (cyclicHomAuxiliaryPoint n f).appTop.hom) :
    cyclicHomNormalizedPoint n f = f := by
  apply cyclicHomPoint_ext n
  · rw [cyclicHomNormalizedPoint_auxiliary, auxiliarySchemeNormalizedPoint_fixed _ hn]
    rfl
  · intro c
    rw [cyclicHomNormalizedPoint_value_normalize]
    exact auxiliarySchemeNormalizedValue_fixed _ hn _ _

end FLT.Mazur.OddWeierstrassParameter
