/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductUniversalSubgroup
public import FLT.Mazur.CyclicCharacteristicProductSubgroupAffineCurve
public import FLT.Mazur.GeneralizedComparisonBetweenRestriction

/-!
# Actual compatible universal comparisons on original-family tests

Pullback of the glued subgroup comparison retains both original subgroups
and the full universal curve. On affine tests it equals the given classifier.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "s" => productComparisonStructure n b c
local notation "i" => productSubgroupInclusion n b c
local notation "H" => productComparisonLeftSubgroup n b c
local notation "J" => productComparisonRightSubgroup n b c

/-- Restrict the compatible universal comparison and retain the original subgroup base maps. -/
def productUniversalSubgroupComparisonOnTest {T : Scheme}
    (k : T ⟶ productSubgroupScheme n b c)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
    (hq : q = (k ≫ i) ≫ (s ≫ prod.fst)) (hr : r = (k ≫ i) ≫ (s ≫ prod.snd)) :
    CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r) :=
  (compatibleBaseChangeCompEq (normalizedSubgroup n b) (s ≫ prod.fst) (k ≫ i) q hq).trans
    ((compatibleBaseChangeComp H i k).trans
      (((productUniversalSubgroupComparison n b c).baseChange k).trans
        ((compatibleBaseChangeComp J i k).symm.trans
          (compatibleBaseChangeCompEq (normalizedSubgroup n c)
            (s ≫ prod.snd) (k ≫ i) r hr).symm)))

/-- The actual compatible pullback retains the prescribed global universal full curve. -/
theorem productUniversalSubgroupComparisonOnTest_curve {T : Scheme}
    (k : T ⟶ productSubgroupScheme n b c)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
    (hq : q = (k ≫ i) ≫ (s ≫ prod.fst)) (hr : r = (k ≫ i) ≫ (s ≫ prod.snd)) :
    (productUniversalSubgroupComparisonOnTest n b c k q r hq hr).curve =
      productUniversalComparisonOnTest n b c (k ≫ i) q r hq hr := by
  simp only [productUniversalSubgroupComparisonOnTest, CompatibleIso.trans, CompatibleIso.symm,
    CompatibleIso.baseChange, compatibleBaseChangeCompEq_curve,
    productUniversalSubgroupComparison_curve]
  exact comparisonPullbackBetween_iterated (normalizedCurve n b) (normalizedCurve n c)
    (s ≫ prod.fst) (s ≫ prod.snd) i k q r hq hr (productUniversalComparison n b c)

variable (U : (normalizedProduct n b c).affineOpens)
  (B : Type) [CommRing B] [Algebra (DirectedAffineSpectrum.Ring
    (normalizedProduct n b c) U) B]
local notation "t" => Spec.algebraMap (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) B
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U

/-- The affine compatible classifier is the actual compatible universal pullback. -/
theorem productSubgroupAffinePointEquiv_universal
    (k : {k : Spec (.of B) ⟶ productSubgroupScheme n b c //
      k ≫ productSubgroupStructure n b c = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι}) :
    productSubgroupAffinePointEquiv n b c U B k =
      productUniversalSubgroupComparisonOnTest n b c k.val (t ≫ L) (t ≫ R)
        (productComparisonAffineTest_left n b c U B (productSubgroupAffineForget n b c U B k))
        (productComparisonAffineTest_right n b c U B
          (productSubgroupAffineForget n b c U B k)) := by
  apply CompatibleIso.ext_curve
  rw [productUniversalSubgroupComparisonOnTest_curve,
    productSubgroupAffinePointEquiv_universal_curve]

/-- Every original compatible affine comparison is recovered by exactly one global test map. -/
theorem productUniversalSubgroupComparisonOnAffineTest_unique
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange (t ≫ L))
      ((normalizedSubgroup n c).baseChange (t ≫ R))) :
    ∃! k : {k : Spec (.of B) ⟶ productSubgroupScheme n b c //
        k ≫ productSubgroupStructure n b c = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι},
      productUniversalSubgroupComparisonOnTest n b c k.val (t ≫ L) (t ≫ R)
        (productComparisonAffineTest_left n b c U B (productSubgroupAffineForget n b c U B k))
        (productComparisonAffineTest_right n b c U B (productSubgroupAffineForget n b c U B k)) =
          a := by
  simpa only [← productSubgroupAffinePointEquiv_universal] using
    (productSubgroupAffinePointEquiv n b c U B).bijective.existsUnique a

end FLT.Mazur.CyclicCharacteristicAtlas
