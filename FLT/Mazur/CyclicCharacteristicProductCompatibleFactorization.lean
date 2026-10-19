/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductSchemeClassification

/-!
# Factoring original compatible comparisons through the subgroup locus

A full parameter recovering a compatible original-family comparison factors
through the actual closed subgroup comparison scheme. The compatible datum
is transported to the universal families before applying their locus criterion.
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

/-- A full parameter recovering a compatible original comparison lies in the subgroup locus. -/
theorem productCompatibleParameter_factorization
    (f : T ⟶ productComparisonScheme n b c)
    (hq : q = f ≫ (s ≫ prod.fst)) (hr : r = f ≫ (s ≫ prod.snd))
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r))
    (ha : productUniversalComparisonOnTest n b c f q r hq hr = a.curve) :
    ∃ k : T ⟶ productSubgroupScheme n b c, k ≫ i = f := by
  apply (productSubgroup_factorization_iff n b c f).mpr
  let A := compatibleBaseChangeCompEq (normalizedSubgroup n b) (s ≫ prod.fst) f q hq
  let B := compatibleBaseChangeCompEq (normalizedSubgroup n c) (s ≫ prod.snd) f r hr
  refine ⟨A.symm.trans (a.trans B), ?_⟩
  change A.curve.symm ≪≫ (a.curve ≪≫ B.curve) = _
  have h : a.curve = A.curve ≪≫
      (baseChangeFunctor f).mapIso (productUniversalComparison n b c) ≪≫ B.curve.symm := by
    simpa only [A, B, compatibleBaseChangeCompEq_curve, productUniversalComparisonOnTest,
      comparisonPullbackBetween] using ha.symm
  rw [h]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.CyclicCharacteristicAtlas
