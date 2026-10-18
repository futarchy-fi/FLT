/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroup
public import FLT.Mazur.CyclicCharacteristicAffineComparisonScheme
public import FLT.Mazur.WeierstrassChangeSubgroupScheme

/-!
# The actual subgroup condition over affine normalized chart products

The transported original subgroups cut out a closed comparison scheme. Its
universal compatible isomorphism compares the original normalized families,
and every test preserves their full subgroup schemes, including non-etale levels.
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
local notation "W" => affineEquation n b q
local notation "V" => affineEquation n c r
local notation "hW" => affineEquation_discriminant n b q
local notation "hV" => affineEquation_discriminant n c r
local notation "H" => affineSubgroup n b q
local notation "J" => affineSubgroup n c r

/-- The closed scheme of subgroup-preserving varying comparisons on an affine chart product. -/
def affineSubgroupScheme : Scheme := subgroupScheme W V hW hV H J

/-- The constructed closed locus retains its entire varying curve parameter. -/
def affineSubgroupInclusion :
    affineSubgroupScheme n b c q r ⟶ affineComparisonScheme n b c q r :=
  subgroupInclusion W V hW hV H J

instance affineSubgroupInclusion_closed :
    IsClosedImmersion (affineSubgroupInclusion n b c q r) :=
  inferInstanceAs (IsClosedImmersion (subgroupInclusion W V hW hV H J))

/-- The original affine chart-product base of the closed comparison locus. -/
def affineSubgroupStructure : affineSubgroupScheme n b c q r ⟶ Spec (.of A) :=
  subgroupStructure W V hW hV H J

/-- The universal compatible comparison retains the original normalized subgroup families. -/
def affineSubgroupUniversalComparison :
    CompatibleIso
      ((normalizedSubgroup n b).baseChange (affineSubgroupStructure n b c q r ≫ q))
      ((normalizedSubgroup n c).baseChange (affineSubgroupStructure n b c q r ≫ r)) :=
  (compatibleBaseChangeComp (normalizedSubgroup n b) q _).trans
    (((affineSubgroupComparison n b q).baseChange _).symm.trans
      ((subgroupUniversalComparison W V hW hV H J).trans
        (((affineSubgroupComparison n c r).baseChange _).trans
          (compatibleBaseChangeComp (normalizedSubgroup n c) r _).symm)))

/-- Every parameter test compares the unchanged original full normalized subgroups. -/
def affineSubgroupComparisonOnTest {T : Scheme} (g : T ⟶ affineSubgroupScheme n b c q r) :
    CompatibleIso
      ((normalizedSubgroup n b).baseChange (g ≫ affineSubgroupStructure n b c q r ≫ q))
      ((normalizedSubgroup n c).baseChange (g ≫ affineSubgroupStructure n b c q r ≫ r)) :=
  (compatibleBaseChangeComp (normalizedSubgroup n b) _ g).trans
    (((affineSubgroupUniversalComparison n b c q r).baseChange g).trans
      (compatibleBaseChangeComp (normalizedSubgroup n c) _ g).symm)

end FLT.Mazur.CyclicCharacteristicAtlas
