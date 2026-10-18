/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationSubgroup

/-!
# The full odd normalization relation retains the original Cartier subgroups

Equal normalized parameters identify the entire original subgroups through
the actual normalization comparisons. Repeated orbit factors remain present.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Equality of actual full parameters retains their full original subgroups. -/
def cyclicHomSubgroupParameterIso (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : f = g) (hf : cyclicHomMultiplicationEquation n f = 0)
    (hg : cyclicHomMultiplicationEquation n g = 0) :
    CompatibleIso (cyclicHomSubgroup n f hf) (cyclicHomSubgroup n g hg) := by
  subst g
  exact CompatibleIso.refl _

/-- Equal complete normalizations give an actual compatible isomorphism of original subgroups. -/
def cyclicHomNormalizationRelationSubgroupIso
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g)
    (hf : cyclicHomMultiplicationEquation n f = 0)
    (hg : cyclicHomMultiplicationEquation n g = 0) :
    CompatibleIso (cyclicHomSubgroup n f hf) (cyclicHomSubgroup n g hg) :=
  (cyclicHomNormalizationSubgroupIso n f hf).symm.trans
    ((cyclicHomSubgroupParameterIso n _ _ h _ _).trans
      (cyclicHomNormalizationSubgroupIso n g hg))

/-- The represented full normalization relation preserves the original ample modular class. -/
theorem cyclicHomSourceModuliClass_of_normalized_eq
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g)
    (hf : cyclicHomMultiplicationEquation n f = 0)
    (hg : cyclicHomMultiplicationEquation n g = 0) :
    cyclicHomSourceModuliClass n f hf = cyclicHomSourceModuliClass n g hg :=
  Quotient.sound ⟨cyclicHomNormalizationRelationSubgroupIso n f g h hf hg⟩

end FLT.Mazur.OddWeierstrassParameter
