/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductCompatibleFactorization

/-!
# Compatible original-family classification on arbitrary scheme tests

Every compatible comparison determines a unique actual map into the glued
subgroup comparison scheme. Recovery retains the entire full curve and the
finite subgroup inclusion on the original families.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool) {T : Scheme}
  (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
local notation "s" => productComparisonStructure n b c
local notation "i" => productSubgroupInclusion n b c
local notation "ss" => productSubgroupStructure n b c
local notation "p" => prod.lift q r

/-- Forgetting a subgroup parameter retains the given ordered pair of original bases. -/
theorem productSubgroupPairTest_base
    (k : {k : T ⟶ productSubgroupScheme n b c // k ≫ ss = p}) :
    (k.val ≫ i) ≫ s = p := by
  rw [Category.assoc, productSubgroupInclusion_structure, k.property]

/-- Evaluate the actual compatible universal comparison over the given original base maps. -/
def productCompatibleTestComparison
    (k : {k : T ⟶ productSubgroupScheme n b c // k ≫ ss = p}) :
    CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r) :=
  productUniversalSubgroupComparisonOnTest n b c k.val q r
    (productPairTest_left n b c q r _ (productSubgroupPairTest_base n b c q r k))
    (productPairTest_right n b c q r _ (productSubgroupPairTest_base n b c q r k))

/-- Evaluation retains the full comparison of the forgotten actual parameter. -/
theorem productCompatibleTestComparison_curve
    (k : {k : T ⟶ productSubgroupScheme n b c // k ≫ ss = p}) :
    (productCompatibleTestComparison n b c q r k).curve =
      productUniversalComparisonOnTest n b c (k.val ≫ i) q r
        (productPairTest_left n b c q r _ (productSubgroupPairTest_base n b c q r k))
        (productPairTest_right n b c q r _ (productSubgroupPairTest_base n b c q r k)) :=
  productUniversalSubgroupComparisonOnTest_curve n b c k.val q r _ _

/-- Every compatible original comparison on an arbitrary scheme has a unique subgroup parameter. -/
theorem productCompatibleTestComparison_existsUnique
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r)) :
    ∃! k : {k : T ⟶ productSubgroupScheme n b c // k ≫ ss = p},
      productCompatibleTestComparison n b c q r k = a := by
  let f := productComparisonParameter n b c q r a.curve
  have hf : f ≫ s = p := productComparisonParameter_base n b c q r a.curve
  have ha := productComparisonParameter_recovers n b c q r a.curve
  obtain ⟨k, hk⟩ := productCompatibleParameter_factorization n b c q r f
    (productPairTest_left n b c q r f hf) (productPairTest_right n b c q r f hf) a ha
  have hb : k ≫ ss = p := by
    rw [← productSubgroupInclusion_structure, ← Category.assoc, hk]
    exact hf
  have hc : productCompatibleTestComparison n b c q r ⟨k, hb⟩ = a := by
    apply CompatibleIso.ext_curve
    rw [productCompatibleTestComparison_curve]
    simpa only [hk] using ha
  refine ⟨⟨k, hb⟩, hc, ?_⟩
  intro z hz
  apply Subtype.ext
  apply (cancel_mono i).mp
  apply productRecoveringParameter_unique n b c q r a.curve
    (z.val ≫ i) (k ≫ i) (productSubgroupPairTest_base n b c q r z)
    (productSubgroupPairTest_base n b c q r ⟨k, hb⟩)
  · exact (productCompatibleTestComparison_curve n b c q r z).symm.trans
      (congrArg CompatibleIso.curve hz)
  · exact (productCompatibleTestComparison_curve n b c q r ⟨k, hb⟩).symm.trans
      (congrArg CompatibleIso.curve hc)

/-- The actual compatible universal comparison classifies all original-family scheme tests. -/
def productCompatibleSchemePointEquiv :
    {k : T ⟶ productSubgroupScheme n b c // k ≫ ss = p} ≃
    CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r) :=
  Equiv.ofBijective (productCompatibleTestComparison n b c q r) (by
    constructor
    · intro x y h
      obtain ⟨z, _, hz⟩ := productCompatibleTestComparison_existsUnique n b c q r
        (productCompatibleTestComparison n b c q r y)
      exact (hz x h).trans (hz y rfl).symm
    · intro a
      obtain ⟨k, hk, _⟩ := productCompatibleTestComparison_existsUnique n b c q r a
      exact ⟨k, hk⟩)

/-- The classifier is evaluation of the actual global compatible universal comparison. -/
theorem productCompatibleSchemePointEquiv_apply
    (k : {k : T ⟶ productSubgroupScheme n b c // k ≫ ss = p}) :
    productCompatibleSchemePointEquiv n b c q r k =
      productCompatibleTestComparison n b c q r k := rfl

end FLT.Mazur.CyclicCharacteristicAtlas
