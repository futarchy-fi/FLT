/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSubgroupPointClassification
public import FLT.Mazur.GeneralizedComparisonPullbackTower

/-!
# Closed-locus classification is the actual universal subgroup pullback

The compatible comparison obtained from the point classifier equals the
restriction of the constructed universal subgroup comparison, with the
original coefficient-base map retained explicitly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) {n : ℕ}
  (H : (integralGeneralizedEllipticCurve W hW).FiniteSubgroup n)
  (J : (integralGeneralizedEllipticCurve V hV).FiniteSubgroup n)
local notation "q" => comparisonStructure W V
local notation "i" => subgroupInclusion W V hW hV H J
local notation "s" => subgroupStructure W V hW hV H J

/-- Restrict the constructed universal subgroup comparison to any named original-base test. -/
def subgroupUniversalOnTest {T : Scheme} (k : T ⟶ subgroupScheme W V hW hV H J)
    (t : T ⟶ Spec (.of R)) (ht : t = k ≫ s) :
    CompatibleIso (H.baseChange t) (J.baseChange t) :=
  (compatibleBaseChangeCompEq H s k t ht).trans
    (((subgroupUniversalComparison W V hW hV H J).baseChange k).trans
      (compatibleBaseChangeCompEq J s k t ht).symm)

/-- Restricting the universal subgroup comparison retains its original full parameter map. -/
theorem subgroupUniversalOnTest_curve {T : Scheme}
    (k : T ⟶ subgroupScheme W V hW hV H J) (t : T ⟶ Spec (.of R)) (ht : t = k ≫ s) :
    (subgroupUniversalOnTest W V hW hV H J k t ht).curve =
      comparisonPullback _ _ q (k ≫ i) t (ht.trans (Category.assoc k i q).symm)
        (universalGeneralizedComparison W V hW hV) := by
  simp only [subgroupUniversalOnTest, CompatibleIso.trans, CompatibleIso.symm,
    compatibleBaseChangeCompEq_curve, CompatibleIso.baseChange]
  change comparisonPullback _ _ s k t ht
    (subgroupUniversalComparison W V hW hV H J).curve = _
  rw [subgroupUniversalComparison_curve]
  exact comparisonPullback_tower _ _ q i k s t rfl ht _

variable (A : Type) [CommRing A] [Algebra R A]

/-- The closed point classifier is exactly pullback of the actual universal subgroup family. -/
theorem subgroupPointEquiv_universal
    (k : {k : Spec (.of A) ⟶ subgroupScheme W V hW hV H J //
      k ≫ s = Spec.algebraMap R A}) :
    subgroupPointEquiv W V hW hV H J A k =
      subgroupUniversalOnTest W V hW hV H J k.val (Spec.algebraMap R A) k.property.symm := by
  apply CompatibleIso.ext_curve
  rw [subgroupPointEquiv_curve, subgroupUniversalOnTest_curve]
  rfl

end FLT.Mazur.WeierstrassChangeParameter
