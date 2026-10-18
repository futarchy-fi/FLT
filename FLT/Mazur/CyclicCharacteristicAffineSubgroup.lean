/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineEquation
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# Retaining normalized subgroups in the affine Weierstrass presentation

Transport changes only the embedding into the full curve. The carrier, every
Cartier generator, and the compatible comparison to the original family remain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassIntegralChart GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) {A : Type} [CommRing A]
  (q : Spec (.of A) ⟶ normalizedLocus n b)

/-- The original finite subgroup, embedded in its concrete affine Weierstrass model. -/
def affineSubgroup :
    (integralGeneralizedEllipticCurve (affineEquation n b q)
      (affineEquation_discriminant n b q)).FiniteSubgroup n :=
  ((normalizedSubgroup n b).baseChange q).transport (affineEquationIso n b q).symm

/-- The affine presentation preserves the entire original finite subgroup compatibly. -/
def affineSubgroupComparison :
    CompatibleIso (affineSubgroup n b q) ((normalizedSubgroup n b).baseChange q) :=
  (((normalizedSubgroup n b).baseChange q).transportCompatibleIso
    (affineEquationIso n b q).symm).symm

/-- The comparison uses exactly the constructed full affine equation isomorphism. -/
theorem affineSubgroupComparison_curve :
    (affineSubgroupComparison n b q).curve = affineEquationIso n b q := rfl

/-- The affine presentation retains the actual carrier, including nonreduced subgroup fibers. -/
theorem affineSubgroup_carrier :
    (affineSubgroup n b q).carrier = ((normalizedSubgroup n b).baseChange q).carrier := rfl

/-- Every original Cartier generator remains a generator on the affine presentation. -/
theorem affineSubgroup_cartierGenerator
    {P : 𝟙_ (Over (Spec (.of A))) ⟶ ((normalizedSubgroup n b).baseChange q).carrier}
    (hP : ((normalizedSubgroup n b).baseChange q).IsCartierGenerator P) :
    (affineSubgroup n b q).IsCartierGenerator P :=
  ((normalizedSubgroup n b).baseChange q).transport_cartierGenerator
    (affineEquationIso n b q).symm hP

end FLT.Mazur.CyclicCharacteristicAtlas
