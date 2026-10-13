/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedRetainedSubgroup
public import FLT.Mazur.OddWeierstrassCyclicHomLocusEquationUniversal
public import FLT.Mazur.OddWeierstrassCyclicHomUniversalSubgroupComparison

/-!
# Actual normalized subgroup-locus parameters on the odd chart

The unchanged original Cartier subgroup forces the multiplication equation.
Its normalized parameter factors through the closed locus and the universal
subgroup recovers the entire original family, also in characteristic two.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {n : ℕ} [NeZero n]
  (p : (Over.map (auxiliaryCoefficientBase g)).obj (𝟙_ (Over (Spec (.of R)))) ⟶ levelThree)
  (H : (auxiliaryPullbackCurve g).FiniteSubgroup n)
  {P : 𝟙_ (Over (Spec (.of R))) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "φ" => H.generatorCurveMarking hP
local notation "f" => Over.Hom.left (auxiliaryNormalizedCyclicParameter g p φ)

/-- The actual original subgroup forces the whole normalized multiplication equation. -/
theorem auxiliaryNormalizedSubgroupEquation : cyclicHomMultiplicationEquation n f = 0 :=
  cyclicHomMultiplicationEquation_of_subgroup n f
    (auxiliaryCyclicSourceRetainedSubgroup g p φ H)
    (auxiliaryCyclicSourceRetained_ideal g p φ H hP rfl)

/-- The normalized original subgroup has an actual parameter in the closed odd-chart locus. -/
def auxiliaryNormalizedSubgroupLocusPoint :
    Spec (.of R) ⟶ cyclicHomUniversalMultiplicationLocus n :=
  cyclicHomUniversalLocusLift n f (auxiliaryNormalizedSubgroupEquation g p H hP)

/-- The factorization keeps all normalized auxiliary labels and original cyclic labels. -/
@[reassoc] theorem auxiliaryNormalizedSubgroupLocusPoint_inclusion :
    auxiliaryNormalizedSubgroupLocusPoint g p H hP ≫
      cyclicHomUniversalMultiplicationLocusInclusion n = f :=
  cyclicHomUniversalLocusLift_inclusion n f _

/-- The universal subgroup at this normalized point retains the complete original subgroup. -/
def auxiliaryNormalizedSubgroupLocusIso :
    CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange
      (auxiliaryNormalizedSubgroupLocusPoint g p H hP)) H :=
  (cyclicHomUniversalSubgroupIsoOfFactorization n
    (auxiliaryNormalizedSubgroupLocusPoint g p H hP) f
    (auxiliaryNormalizedSubgroupLocusPoint_inclusion g p H hP)
    (auxiliaryCyclicSourceRetainedSubgroup g p φ H)
    (auxiliaryCyclicSourceRetained_ideal g p φ H hP rfl)).trans
      (auxiliaryCyclicSourceRetainedIso g p φ H).symm

end FLT.Mazur.OddWeierstrassParameter
