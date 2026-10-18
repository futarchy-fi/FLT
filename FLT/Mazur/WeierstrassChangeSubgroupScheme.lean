/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeGeneralizedComparison
public import FLT.Mazur.WeierstrassChangeComparisonScheme
public import FLT.Mazur.FiniteSubgroupComparisonLocus

/-!
# The closed subgroup condition on varying full curve comparisons

The actual comparison scheme now carries a closed subscheme on which the
original full finite subgroups compare. Its universal comparison is between
the original families over the composite parameter map. No Cartier generator,
etaleness, or reduced-support condition is imposed.
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
local notation "e" => universalGeneralizedComparison W V hW hV

/-- The actual closed parameter scheme preserving the whole original finite subgroups. -/
def subgroupScheme : Scheme :=
  subgroupComparisonLocus (H.baseChange q) (J.baseChange q) e

/-- Forgetting the subgroup condition retains the varying full curve comparison parameter. -/
def subgroupInclusion : subgroupScheme W V hW hV H J ⟶ comparisonScheme W V :=
  subgroupComparisonLocusInclusion (H.baseChange q) (J.baseChange q) e

instance subgroupInclusion_closed : IsClosedImmersion (subgroupInclusion W V hW hV H J) :=
  inferInstanceAs (IsClosedImmersion
    (subgroupComparisonLocusInclusion (H.baseChange q) (J.baseChange q) e))

/-- The original coefficient-base map of the varying compatible subgroup parameter. -/
def subgroupStructure : subgroupScheme W V hW hV H J ⟶ Spec (.of R) :=
  subgroupInclusion W V hW hV H J ≫ q

/-- The universal relation is an actual compatible comparison of the original full families. -/
def subgroupUniversalComparison :
    CompatibleIso (H.baseChange (subgroupStructure W V hW hV H J))
      (J.baseChange (subgroupStructure W V hW hV H J)) :=
  (compatibleBaseChangeComp H q (subgroupInclusion W V hW hV H J)).trans
    ((subgroupComparisonLocusCompatibleIso (H.baseChange q) (J.baseChange q) e).trans
      (compatibleBaseChangeComp J q (subgroupInclusion W V hW hV H J)).symm)

/-- The scheme-theoretic subgroup condition keeps the full specified varying curve map. -/
theorem subgroupInclusion_factorization_iff {T : Scheme} (g : T ⟶ comparisonScheme W V) :
    (∃ k : T ⟶ subgroupScheme W V hW hV H J,
      k ≫ subgroupInclusion W V hW hV H J = g) ↔
      ∃ a : CompatibleIso ((H.baseChange q).baseChange g) ((J.baseChange q).baseChange g),
        a.curve = (((H.baseChange q).transportCompatibleIso e).baseChange g).curve :=
  subgroupComparisonLocus_factorization_iff (H.baseChange q) (J.baseChange q) e g

/-- Every test of the closed parameter scheme compares the unchanged original full subgroups. -/
def subgroupComparisonOnTest {T : Scheme} (g : T ⟶ subgroupScheme W V hW hV H J) :
    CompatibleIso (H.baseChange (g ≫ subgroupStructure W V hW hV H J))
      (J.baseChange (g ≫ subgroupStructure W V hW hV H J)) :=
  (compatibleBaseChangeComp H (subgroupStructure W V hW hV H J) g).trans
    (((subgroupUniversalComparison W V hW hV H J).baseChange g).trans
      (compatibleBaseChangeComp J (subgroupStructure W V hW hV H J) g).symm)

end FLT.Mazur.WeierstrassChangeParameter
