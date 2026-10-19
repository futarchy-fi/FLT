/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupUniversalCurve
public import FLT.Mazur.WeierstrassSubgroupPointClassification

/-!
# Local closed-subgroup classification for the original normalized families

The actual closed comparison scheme classifies every original compatible
comparison on affine tests, keeping its full curve map and all automorphisms.
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
local notation "s" => affineComparisonStructure n b c q r
local notation "i" => affineSubgroupInclusion n b c q r
variable (B : Type) [CommRing B] [Algebra A B]
local notation "t" => Spec.algebraMap A B

/-- The subgroup presentation on a test retains the original composite normalized base map. -/
def affineSubgroupTestTransport :
    CompatibleIso ((H).baseChange t) ((normalizedSubgroup n b).baseChange (t ≫ q)) :=
  ((affineSubgroupComparison n b q).baseChange t).trans
    (compatibleBaseChangeComp (normalizedSubgroup n b) q t).symm

/-- Actual closed-locus tests classify every compatible isomorphism of the original subgroups. -/
def affineSubgroupPointEquiv :
    {k : Spec (.of B) ⟶ affineSubgroupScheme n b c q r //
      k ≫ affineSubgroupStructure n b c q r = t} ≃
      CompatibleIso ((normalizedSubgroup n b).baseChange (t ≫ q))
        ((normalizedSubgroup n c).baseChange (t ≫ r)) :=
  (subgroupPointEquiv W V hW hV H J B).trans
    (compatibleIsoCongr (affineSubgroupTestTransport n b q B)
      (affineSubgroupTestTransport n c r B))

/-- The local closed classifier retains exactly the universal full comparison on its test. -/
theorem affineSubgroupPointEquiv_curve
    (k : {k : Spec (.of B) ⟶ affineSubgroupScheme n b c q r //
      k ≫ affineSubgroupStructure n b c q r = t}) :
    (affineSubgroupPointEquiv n b c q r B k).curve =
      affineUniversalComparisonOnTest n b c q r B (subgroupTestForget i s t k) := by
  change (affineSubgroupTestTransport n b q B).curve.symm ≪≫
    (subgroupPointEquiv W V hW hV H J B k).curve ≪≫
      (affineSubgroupTestTransport n c r B).curve = _
  rw [subgroupPointEquiv_curve]
  unfold affineUniversalComparisonOnTest affineUniversalComparison
  rw [comparisonPullback_natural]
  apply Iso.ext
  simp only [affineSubgroupTestTransport, CompatibleIso.trans, CompatibleIso.symm,
    CompatibleIso.baseChange, affineSubgroupComparison_curve, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rfl

/-- Every original compatible comparison has exactly one closed-locus parameter. -/
theorem affineSubgroupPointEquiv_unique
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange (t ≫ q))
      ((normalizedSubgroup n c).baseChange (t ≫ r))) :
    ∃! k : {k : Spec (.of B) ⟶ affineSubgroupScheme n b c q r //
      k ≫ affineSubgroupStructure n b c q r = t},
      affineSubgroupPointEquiv n b c q r B k = a :=
  (affineSubgroupPointEquiv n b c q r B).bijective.existsUnique a

end FLT.Mazur.CyclicCharacteristicAtlas
