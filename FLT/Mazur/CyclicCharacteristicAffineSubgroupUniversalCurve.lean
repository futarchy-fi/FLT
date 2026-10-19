/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupScheme
public import FLT.Mazur.CyclicCharacteristicAffineUniversalComparison
public import FLT.Mazur.WeierstrassSubgroupUniversalCurve

/-!
# The original affine subgroup comparison is the universal curve restriction

The closed subgroup locus keeps exactly the varying full comparison on the
original normalized families. All base-map transports remain explicit.
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
local notation "i" => affineSubgroupInclusion n b c q r
local notation "t" => affineSubgroupStructure n b c q r

/-- The closed subgroup comparison retains precisely the original universal full curve map. -/
theorem affineSubgroupUniversalComparison_curve :
    (affineSubgroupUniversalComparison n b c q r).curve =
      (normalizedCurve n b).baseChangeCompIso q t ≪≫
        comparisonPullback _ _ s i t rfl (affineUniversalComparison n b c q r) ≪≫
          ((normalizedCurve n c).baseChangeCompIso r t).symm := by
  unfold affineUniversalComparison
  rw [comparisonPullback_natural]
  change (normalizedCurve n b).baseChangeCompIso q t ≪≫
    (((baseChangeFunctor t).mapIso (affineEquationIso n b q)).symm ≪≫
      (subgroupUniversalComparison (affineEquation n b q) (affineEquation n c r)
        (affineEquation_discriminant n b q) (affineEquation_discriminant n c r)
        (affineSubgroup n b q) (affineSubgroup n c r)).curve ≪≫
      ((baseChangeFunctor t).mapIso (affineEquationIso n c r)) ≪≫
        ((normalizedCurve n c).baseChangeCompIso r t).symm) = _
  rw [subgroupUniversalComparison_curve]
  apply Iso.ext
  simp only [Iso.trans_hom, Category.assoc]
  rfl

end FLT.Mazur.CyclicCharacteristicAtlas
