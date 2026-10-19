/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductCompatibleTests

/-!
# Restriction compatibility of the actual universal comparisons

Further restriction of an original-family comparison agrees with composition
of its parameter map. This holds for every scheme test, with both the full
curve and its compatible finite subgroup retained.
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
variable {T V : Scheme} (l : V ⟶ T)
  (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
  (v : V ⟶ normalizedLocus n b) (w : V ⟶ normalizedLocus n c)
  (hv : v = l ≫ q) (hw : w = l ≫ r)

/-- Full universal comparison restriction agrees with the composite actual parameter map. -/
theorem productUniversalComparisonOnTest_restrict
    (f : T ⟶ productComparisonScheme n b c)
    (hq : q = f ≫ (s ≫ prod.fst)) (hr : r = f ≫ (s ≫ prod.snd)) :
    comparisonPullbackBetween (normalizedCurve n b) (normalizedCurve n c) q r l v w hv hw
        (productUniversalComparisonOnTest n b c f q r hq hr) =
      productUniversalComparisonOnTest n b c (l ≫ f) v w
        (hv.trans ((congrArg (l ≫ ·) hq).trans (Category.assoc _ _ _).symm))
        (hw.trans ((congrArg (l ≫ ·) hr).trans (Category.assoc _ _ _).symm)) :=
  comparisonPullbackBetween_restrict (normalizedCurve n b) (normalizedCurve n c)
    (s ≫ prod.fst) (s ≫ prod.snd) f l v w q r hq hr hv hw
    (productUniversalComparison n b c)

include hv in
/-- The composite subgroup parameter retains the original left endpoint after restriction. -/
theorem productSubgroupTest_restrict_left (k : T ⟶ productSubgroupScheme n b c)
    (hq : q = (k ≫ i) ≫ (s ≫ prod.fst)) :
    v = ((l ≫ k) ≫ i) ≫ (s ≫ prod.fst) := by
  rw [hv, hq]
  simp only [Category.assoc]

include hw in
/-- The composite subgroup parameter retains the original right endpoint after restriction. -/
theorem productSubgroupTest_restrict_right (k : T ⟶ productSubgroupScheme n b c)
    (hr : r = (k ≫ i) ≫ (s ≫ prod.snd)) :
    w = ((l ≫ k) ≫ i) ≫ (s ≫ prod.snd) := by
  rw [hw, hr]
  simp only [Category.assoc]

/-- Restriction recovers the full compatible comparison of the composed subgroup parameter. -/
theorem productUniversalSubgroupComparisonOnTest_restrict
    (k : T ⟶ productSubgroupScheme n b c)
    (hq : q = (k ≫ i) ≫ (s ≫ prod.fst)) (hr : r = (k ≫ i) ≫ (s ≫ prod.snd)) :
    (compatibleBaseChangeCompEq (normalizedSubgroup n b) q l v hv).trans
        (((productUniversalSubgroupComparisonOnTest n b c k q r hq hr).baseChange l).trans
          (compatibleBaseChangeCompEq (normalizedSubgroup n c) r l w hw).symm) =
      productUniversalSubgroupComparisonOnTest n b c (l ≫ k) v w
        (productSubgroupTest_restrict_left n b c l q v hv k hq)
        (productSubgroupTest_restrict_right n b c l r w hw k hr) := by
  apply CompatibleIso.ext_curve
  simp only [CompatibleIso.trans, CompatibleIso.symm, CompatibleIso.baseChange,
    compatibleBaseChangeCompEq_curve, productUniversalSubgroupComparisonOnTest_curve]
  have h := productUniversalComparisonOnTest_restrict n b c l q r v w hv hw (k ≫ i) hq hr
  change comparisonPullbackBetween (normalizedCurve n b) (normalizedCurve n c)
    q r l v w hv hw (productUniversalComparisonOnTest n b c (k ≫ i) q r hq hr) =
      productUniversalComparisonOnTest n b c ((l ≫ k) ≫ i) v w _ _
  simpa only [Category.assoc] using h

end FLT.Mazur.CyclicCharacteristicAtlas
