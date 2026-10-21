/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularProduct
public import FLT.Mazur.CyclicMarkingGroupIdealBaseChange
public import FLT.Mazur.ClosedGroupIdealEquationBaseChange

/-!
# The singular cyclic multiplication ideal under arbitrary base change

The full product and its obstruction ideal commute with every parameter
change before the multiplication equation is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group)) (g : T ⟶ S)

/-- The original parameter map on the entire singular orbit product. -/
def singularOrbitProductBaseChangeMap :
    ((E.baseChange g).singularOrbitProduct (pullCyclicMarking (E := E) g φ)).left ⟶
      (E.singularOrbitProduct φ).left :=
  ClosedGroupIdeal.productBaseChangeMap E.group (E.cyclicMarkingGroupIdeal φ) g _
    (E.cyclicMarkingGroupIdeal_baseChange φ g).symm

/-- The product of full orbit divisors is cartesian over any new parameter base. -/
theorem singularOrbitProductBaseChangeMap_isPullback :
    IsPullback (E.singularOrbitProductBaseChangeMap φ g)
      ((E.baseChange g).singularOrbitProduct (pullCyclicMarking (E := E) g φ)).hom
      (E.singularOrbitProduct φ).hom g :=
  ClosedGroupIdeal.productBaseChangeMap_isPullback E.group (E.cyclicMarkingGroupIdeal φ) g _
    (E.cyclicMarkingGroupIdeal_baseChange φ g).symm

/-- The obstruction ideal, not just its vanishing, is the actual pulled-back ideal. -/
theorem singularOrbitMultiplicationIdeal_baseChange :
    (E.baseChange g).singularOrbitMultiplicationIdeal (pullCyclicMarking (E := E) g φ) =
      (E.singularOrbitMultiplicationIdeal φ).comap (E.singularOrbitProductBaseChangeMap φ g) :=
  ClosedGroupIdeal.multiplicationImage_baseChange E.group (E.cyclicMarkingGroupIdeal φ) g _
    (E.cyclicMarkingGroupIdeal_baseChange φ g).symm

variable [SmoothOfRelativeDimension 1 E.group.hom]

/-- The source comparison for the singular equation is an actual module isomorphism. -/
theorem singularOrbitEquationSource_isIso :
    IsIso (ClosedGroupIdeal.multiplicationEquationBaseChangeSource E.group
      (E.cyclicMarkingGroupIdeal φ) g _ (E.cyclicMarkingGroupIdeal_baseChange φ g).symm) := by
  let _ := E.cyclicMarkingGroupIdeal_pullback_isIso φ g
  infer_instance

omit [SmoothOfRelativeDimension 1 E.group.hom] in
/-- The original module equation is pulled back with its full source and target comparisons. -/
theorem singularOrbitEquation_baseChange :
    (Scheme.Modules.pullback (E.singularOrbitProductBaseChangeMap φ g)).map
        (ClosedGroupIdeal.multiplicationEquation E.group (E.cyclicMarkingGroupIdeal φ)) ≫
          (FCurve.modulePullbackUnitIso (E.singularOrbitProductBaseChangeMap φ g)).hom =
      ClosedGroupIdeal.multiplicationEquationBaseChangeSource E.group
          (E.cyclicMarkingGroupIdeal φ) g _ (E.cyclicMarkingGroupIdeal_baseChange φ g).symm ≫
        ClosedGroupIdeal.multiplicationEquation (E.baseChange g).group
          ((E.baseChange g).cyclicMarkingGroupIdeal (pullCyclicMarking (E := E) g φ)) :=
  ClosedGroupIdeal.multiplicationEquation_baseChange E.group (E.cyclicMarkingGroupIdeal φ) g _
    (E.cyclicMarkingGroupIdeal_baseChange φ g).symm

end FLT.Mazur.GeneralizedEllipticCurve
