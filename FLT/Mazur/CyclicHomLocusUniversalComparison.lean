/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomRelationIsoNaturality
public import FLT.Mazur.CyclicHomRelationIsoCoherence

/-!
# The universal genuine marked comparison on the original subgroup relation

The kernel pair carries a specified comparison of its two original families.
Every test of that scheme pulls back this same comparison, uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "a" => cyclicHomLocusRelationFirst n ≫
  cyclicHomUniversalMultiplicationLocusInclusion n
local notation "b" => cyclicHomLocusRelationSecond n ≫
  cyclicHomUniversalMultiplicationLocusInclusion n

/-- The universal original pair has equal complete normalized parameters. -/
theorem cyclicHomLocusUniversalComparison_eq :
    cyclicHomNormalizedPoint n a = cyclicHomNormalizedPoint n b :=
  (cyclicHomLocusNormalization_eq_iff n _ _).mp (cyclicHomLocusRelation_condition n)

/-- The actual universal independently marked group-family comparison. -/
irreducible_def cyclicHomLocusUniversalComparison :
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n a) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n b) :=
  cyclicHomNormalizationRelationIso n a b (cyclicHomLocusUniversalComparison_eq n)

/-- The universal comparison retains every original auxiliary label. -/
theorem cyclicHomLocusUniversalComparison_auxiliary (c : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n a) c ≫
      (cyclicHomLocusUniversalComparison n).hom.hom.hom.hom =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n b) c := by
  rw [cyclicHomLocusUniversalComparison_def]
  exact cyclicHomNormalizationRelationIso_auxiliary n a b _ c

/-- The universal comparison retains each cyclic label even when sections coincide. -/
theorem cyclicHomLocusUniversalComparison_cyclic (c : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n a c ≫ (cyclicHomLocusUniversalComparison n).hom.hom.hom.hom =
      cyclicHomSourceMarking n b c := by
  rw [cyclicHomLocusUniversalComparison_def]
  exact cyclicHomNormalizationRelationIso_cyclic n a b _ c

/-- Every test of the relation has the same full normalized parameter at both ends. -/
theorem cyclicHomLocusUniversalComparison_test_eq {T : Scheme}
    (r : T ⟶ cyclicHomLocusNormalizationRelation n) :
    cyclicHomNormalizedPoint n (r ≫ a) = cyclicHomNormalizedPoint n (r ≫ b) := by
  rw [cyclicHomNormalizedPoint_natural n a r, cyclicHomNormalizedPoint_natural n b r,
    cyclicHomLocusUniversalComparison_eq]

/-- Every original test comparison is the actual pullback of the universal comparison. -/
theorem cyclicHomLocusUniversalComparison_test {T : Scheme}
    (r : T ⟶ cyclicHomLocusNormalizationRelation n) :
    cyclicHomMarkedIsoPullback n a b (cyclicHomLocusUniversalComparison n) r =
      cyclicHomNormalizationRelationIso n (r ≫ a) (r ≫ b)
        (cyclicHomLocusUniversalComparison_test_eq n r) := by
  rw [cyclicHomLocusUniversalComparison_def]
  exact cyclicHomNormalizationRelationIso_pullback n a b _ r _

/-- A specified auxiliary-marked comparison on a test is exactly the universal comparison there. -/
theorem cyclicHomLocusUniversalComparison_test_unique {T : Scheme}
    (r : T ⟶ cyclicHomLocusNormalizationRelation n)
    (e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n (r ≫ a)) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n (r ≫ b)))
    (ha : ∀ c : Labels 4, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (r ≫ a)) c ≫
      e.hom.hom.hom.hom = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (r ≫ b)) c) :
    e = cyclicHomMarkedIsoPullback n a b (cyclicHomLocusUniversalComparison n) r := by
  rw [cyclicHomLocusUniversalComparison_test]
  exact cyclicHomMarkedIso_eq_normalizationRelation n (r ≫ a) (r ≫ b) _ e ha

end FLT.Mazur.UniversalWeierstrass
