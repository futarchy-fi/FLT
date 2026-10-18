/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteClosedSubgroupIso
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# Complete one-gon subgroup comparison on every original boundary test

The original closed subgroup and its full generalized curve recover the actual
complete-family pullback over arbitrary schemes over the coefficient field.
The comparison retains the full ideal, cyclicity, and ampleness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
local notation "H" => completeFiniteSubgroup K n labels hlabels
local notation "J" => completeClosedFiniteSubgroup K n labels hlabels
variable {T : Scheme} (g : T ⟶ Spec (.of K))

/-- Every original boundary test retains the complete family and subgroup comparison. -/
def completeBoundarySubgroupIso : CompatibleIso ((H).baseChange (g ≫ (c))) ((J).baseChange g) :=
  (compatibleBaseChangeComp (H) (c) g).trans
    ((completeClosedSubgroupIso K n labels hlabels).baseChange g)

/-- The boundary ideal is the full original closed subgroup kernel pulled back to the test. -/
theorem completeBoundarySubgroup_ideal :
    ((J).baseChange g).ideal = (faithfulClosedCurveMap K n labels hlabels).left.ker.comap
      (pullback.fst ((completeGeneralizedCurve K).baseChange (c)).curve.hom g) := by
  rw [baseChange_ideal, completeClosedFiniteSubgroup_ideal]

/-- The actual original boundary subgroup remains cyclic over every scheme test. -/
theorem completeBoundarySubgroup_isCyclic : ((J).baseChange g).IsCyclic :=
  (completeClosedFiniteSubgroup_isCyclic K n labels hlabels).baseChange (J) g

/-- The whole original boundary divisor remains ample over every scheme test. -/
theorem completeBoundarySubgroup_isAmple : ((J).baseChange g).IsAmple :=
  (completeClosedFiniteSubgroup_isAmple K n labels hlabels).baseChange g

end FLT.Mazur.OneGonSmoothing
