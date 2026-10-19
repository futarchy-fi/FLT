/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupScheme
public import FLT.Mazur.CyclicCharacteristicAffineUniversalComparison
public import FLT.Mazur.FiniteSubgroupComparisonLocusPresentation

/-!
# The affine closed subgroup locus in the original normalized families

The constructed coefficient-model subgroup scheme is isomorphic over its
full comparison parameter scheme to the locus in the original families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {A : Type} [CommRing A]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
local notation "s" => affineComparisonStructure n b c q r
local notation "H" => FiniteSubgroup.baseChange
  (FiniteSubgroup.baseChange (normalizedSubgroup n b) q) s
local notation "J" => FiniteSubgroup.baseChange
  (FiniteSubgroup.baseChange (normalizedSubgroup n c) r) s
local notation "e" => affineUniversalComparison n b c q r

/-- The closed locus of the actual universal comparison in the original subgroup families. -/
def affineOriginalSubgroupLocus : Scheme := subgroupComparisonLocus H J e

/-- The original-family locus retains its full varying comparison parameter. -/
def affineOriginalSubgroupInclusion :
    affineOriginalSubgroupLocus n b c q r ⟶ affineComparisonScheme n b c q r :=
  subgroupComparisonLocusInclusion H J e

/-- The concrete affine subgroup scheme is the actual original-family closed locus. -/
def affineOriginalSubgroupLocusIso :
    affineSubgroupScheme n b c q r ≅ affineOriginalSubgroupLocus n b c q r :=
  subgroupComparisonLocusPresentationIso
    ((affineSubgroupComparison n b q).baseChange s)
    ((affineSubgroupComparison n c r).baseChange s)
    (universalGeneralizedComparison (affineEquation n b q) (affineEquation n c r)
      (affineEquation_discriminant n b q) (affineEquation_discriminant n c r))

/-- The identification keeps exactly the original closed immersion into the parameter scheme. -/
@[reassoc] theorem affineOriginalSubgroupLocusIso_inclusion :
    (affineOriginalSubgroupLocusIso n b c q r).hom ≫
      affineOriginalSubgroupInclusion n b c q r = affineSubgroupInclusion n b c q r :=
  subgroupComparisonLocusPresentationIso_inclusion
    ((affineSubgroupComparison n b q).baseChange s)
    ((affineSubgroupComparison n c r).baseChange s)
    (universalGeneralizedComparison (affineEquation n b q) (affineEquation n c r)
      (affineEquation_discriminant n b q) (affineEquation_discriminant n c r))

end FLT.Mazur.CyclicCharacteristicAtlas
