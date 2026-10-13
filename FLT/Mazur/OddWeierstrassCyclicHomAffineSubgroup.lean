/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomAffineMarkings
public import FLT.Mazur.OddWeierstrassNormalizationSubgroup

/-!
# The original finite subgroup on its affine auxiliary cubic

The full affine source comparison retains the subgroup carrier, Cartier
generator, and scheme-theoretic ideal, including nonreduced cyclic subgroups.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {n : ℕ} [NeZero n]
  (f : Spec (.of R) ⟶ (cyclicHomAuxiliaryScheme n).left)
  (H : (cyclicHomSourceCurve n f).FiniteSubgroup n)
local notation "g" => auxiliaryPointSections (cyclicHomAuxiliaryPoint n f)

/-- Retain the actual subgroup on the original auxiliary coefficient cubic. -/
def cyclicHomAffineSubgroup : (auxiliaryPullbackCurve g).FiniteSubgroup n :=
  H.transport (cyclicHomAffineSourceCurveIso n f).symm

/-- The entire original finite subgroup has a compatible curve and carrier comparison. -/
def cyclicHomAffineSubgroupIso : CompatibleIso H (cyclicHomAffineSubgroup f H) :=
  H.transportCompatibleIso (cyclicHomAffineSourceCurveIso n f).symm

/-- Every original scheme-theoretic multiplicity is retained. -/
theorem cyclicHomAffineSubgroup_ideal :
    (cyclicHomAffineSubgroup f H).ideal =
      H.ideal.comap (cyclicHomAffineSourceCurveIso n f).hom.curve.left :=
  ideal_transport H _ (cyclicHomAffineSubgroupIso f H).curve
    (cyclicHomAffineSubgroupIso f H).subgroup (cyclicHomAffineSubgroupIso f H).compatible

variable {P : 𝟙_ (Over (Spec (.of R))) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

include hP in
/-- The identical original generator remains Cartier on the coefficient cubic. -/
theorem cyclicHomAffineSubgroup_generator : (cyclicHomAffineSubgroup f H).IsCartierGenerator P :=
  H.transport_cartierGenerator (cyclicHomAffineSourceCurveIso n f).symm hP

/-- The generator's full cyclic marking is retained by the whole curve comparison. -/
theorem cyclicHomAffineSubgroup_marking (i : Multiplicative (ZMod n)) :
    (cyclicHomAffineSubgroup f H).generatorCurveMarking
        (cyclicHomAffineSubgroup_generator f H hP) i =
      H.generatorCurveMarking hP i ≫ (cyclicHomAffineSourceCurveIso n f).inv.group :=
  H.generatorCurveMarking_transport (cyclicHomAffineSourceCurveIso n f).symm hP i

end FLT.Mazur.OddWeierstrassParameter
