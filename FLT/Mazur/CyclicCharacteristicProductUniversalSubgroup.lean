/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductSubgroupIdentification

/-!
# A full compatible comparison on the actual glued subgroup scheme

The identified closed locus constructs the subgroup comparison on the original
glued parameter scheme. Its full curve is precisely the restricted global comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "H" => productComparisonLeftSubgroup n b c
local notation "J" => productComparisonRightSubgroup n b c
local notation "e" => productUniversalComparison n b c
local notation "i" => productSubgroupInclusion n b c

/-- The original subgroup scheme carries a comparison extending the specified full curve. -/
theorem productUniversalSubgroupComparison_exists :
    ∃ a : CompatibleIso ((H).baseChange i) ((J).baseChange i),
      a.curve = (baseChangeFunctor i).mapIso e := by
  exact (subgroupComparisonLocus_factorization_iff H J e i).mp
    ⟨(productSubgroupLocusIso n b c).hom, productSubgroupLocusIso_inclusion n b c⟩

/-- The full compatible universal comparison on the actual glued subgroup parameter scheme. -/
def productUniversalSubgroupComparison : CompatibleIso ((H).baseChange i) ((J).baseChange i) :=
  (productUniversalSubgroupComparison_exists n b c).choose

/-- The compatible comparison retains the original global universal full curve. -/
theorem productUniversalSubgroupComparison_curve :
    (productUniversalSubgroupComparison n b c).curve = (baseChangeFunctor i).mapIso e :=
  (productUniversalSubgroupComparison_exists n b c).choose_spec

/-- Arbitrary tests of the full parameter scheme factor precisely when its comparison extends. -/
theorem productSubgroup_factorization_iff {T : Scheme} (g : T ⟶ productComparisonScheme n b c) :
    (∃ k : T ⟶ productSubgroupScheme n b c, k ≫ i = g) ↔
      ∃ a : CompatibleIso ((H).baseChange g) ((J).baseChange g),
        a.curve = (baseChangeFunctor g).mapIso e := by
  refine Iff.trans ?_ (subgroupComparisonLocus_factorization_iff H J e g)
  change (∃ k : T ⟶ productSubgroupScheme n b c, k ≫ i = g) ↔
    ∃ k : T ⟶ productOriginalSubgroupLocus n b c,
      k ≫ productOriginalSubgroupInclusion n b c = g
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k ≫ (productSubgroupLocusIso n b c).hom, by
      rw [Category.assoc, productSubgroupLocusIso_inclusion, hk]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k ≫ (productSubgroupLocusIso n b c).inv, ?_⟩
    rw [← productSubgroupLocusIso_inclusion n b c]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hk

end FLT.Mazur.CyclicCharacteristicAtlas
