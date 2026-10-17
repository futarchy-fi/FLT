/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizationRetraction
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationFixed

/-!
# Full cyclic normalization is idempotent on every source

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

/-- Repeated normalization fixes the entire unrestricted cyclic parameter. -/
theorem cyclicHomNormalizedPoint_idempotent (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    cyclicHomNormalizedPoint n (cyclicHomNormalizedPoint n f) = cyclicHomNormalizedPoint n f := by
  apply cyclicHomNormalizedPoint_fixed
  change SatisfiesNormalization
    (cyclicHomNormalizedPoint n f ≫ (cyclicHomAuxiliary n).left).appTop.hom
  rw [cyclicHomNormalizedPoint_auxiliary]
  exact auxiliarySchemeNormalizedPoint_satisfies _

end FLT.Mazur.OddWeierstrassParameter
