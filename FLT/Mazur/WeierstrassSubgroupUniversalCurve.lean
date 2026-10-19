/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeSubgroupScheme
public import FLT.Mazur.GeneralizedComparisonPullbackCoherence

/-!
# The closed subgroup comparison retains the universal full curve map

Restricting the universal full comparison to the closed subgroup locus gives
exactly the curve of its universal compatible subgroup isomorphism.
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
local notation "e" => universalGeneralizedComparison W V hW hV

/-- The compatible universal subgroup comparison has the original universal full curve map. -/
theorem subgroupUniversalComparison_curve :
    (subgroupUniversalComparison W V hW hV H J).curve =
      comparisonPullback _ _ q i s rfl e := by
  change (integralGeneralizedEllipticCurve W hW).baseChangeCompIso q i ≪≫
    (subgroupComparisonLocusCompatibleIso (H.baseChange q) (J.baseChange q) e).curve ≪≫
      ((integralGeneralizedEllipticCurve V hV).baseChangeCompIso q i).symm = _
  rw [subgroupComparisonLocusCompatibleIso_curve]
  have hc (D : GeneralizedEllipticCurve (Spec (.of R))) :
      D.baseChangeCompEqIso q i s rfl = D.baseChangeCompIso q i :=
    Iso.ext (Category.id_comp _)
  unfold comparisonPullback
  rw [hc, hc]
  rfl

end FLT.Mazur.WeierstrassChangeParameter
