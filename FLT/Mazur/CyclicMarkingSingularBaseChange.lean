/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularGenerator

/-!
# Arbitrary base change of singular cyclic orbit subgroups

The full orbit ideal commutes with every base change. Applying the exact
subgroup criterion to the actual pulled-back subgroup proves multiplication
closure on the new base and identifies the newly constructed full subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  [SmoothOfRelativeDimension 1 E.group.hom]
  (hm : ClosedGroupIdeal.multiplicationEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0)
  (g : T ⟶ S)

local instance singularOrbitPullback_smooth :
    SmoothOfRelativeDimension 1 (E.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom g
    inferInstance

/-- The pulled-back subgroup retains the exact orbit ideal on the new whole curve. -/
theorem singularCyclicDivisorSubgroup_baseChange_ideal :
    ((E.singularCyclicDivisorSubgroup φ hm).baseChange g).ideal =
      (E.baseChange g).cyclicMarkingIdeal (pullCyclicMarking (E := E) g φ) := by
  rw [FiniteSubgroup.baseChange_ideal, singularCyclicDivisorSubgroup_ideal,
    cyclicMarkingIdeal_baseChange]

include hm in
/-- The full multiplication equation persists after arbitrary, possibly nonflat base change. -/
theorem singularCyclicMultiplication_baseChange :
    ClosedGroupIdeal.multiplicationEquation (E.baseChange g).group
      ((E.baseChange g).cyclicMarkingGroupIdeal (pullCyclicMarking (E := E) g φ)) = 0 :=
  (E.baseChange g).cyclicMarkingGroupIdeal_multiplication_of_subgroup _
    ((E.singularCyclicDivisorSubgroup φ hm).baseChange g)
    (E.singularCyclicDivisorSubgroup_baseChange_ideal φ hm g)

/-- Reconstructing after base change preserves the full curve, subgroup and inclusion. -/
def singularCyclicDivisorBaseChangeIso :
    FiniteSubgroup.CompatibleIso
      ((E.baseChange g).singularCyclicDivisorSubgroup (pullCyclicMarking (E := E) g φ)
        (E.singularCyclicMultiplication_baseChange φ hm g))
      ((E.singularCyclicDivisorSubgroup φ hm).baseChange g) :=
  (E.baseChange g).singularCyclicDivisorOriginalIso _ _ _
    (E.singularCyclicDivisorSubgroup_baseChange_ideal φ hm g)

end FLT.Mazur.GeneralizedEllipticCurve
