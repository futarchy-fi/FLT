/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteAmpleCyclicSubgroup
public import FLT.Mazur.OneGonFaithfulClosedSubgroup
public import FLT.Mazur.GeneralizedCurveAmpleBaseChange

/-!
# Original complete cyclic subgroups on arbitrary tests

The bundled generalized curve and its finite subgroup retain the actual
whole-curve map and ideal under every base change. On the closed coefficient
fiber the ideal is the original closed subgroup ideal, including multiplicities.
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
local notation "H" => completeFiniteSubgroup K n labels hlabels
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

variable {T : Scheme} (g : T ⟶ Spec (.of (PowerSeries K)))

/-- Every test retains the actual complete whole-curve subgroup map. -/
theorem completeFiniteSubgroup_baseChange_curveMap :
    ((H).baseChange g).curveMap =
      (Over.pullback g).map (faithfulCompleteCurveMap K n labels hlabels) := by
  rw [baseChange_curveMap, completeFiniteSubgroup_curveMap]

/-- Every test retains the full pulled-back original complete subgroup ideal. -/
theorem completeFiniteSubgroup_baseChange_ideal :
    ((H).baseChange g).ideal = (faithfulCompleteIdeal K n labels hlabels).comap
      (pullback.fst (family (t)).hom g) := by
  rw [baseChange_ideal, completeFiniteSubgroup_ideal]
  rfl

/-- The full Cartier generator survives every, possibly nonreduced, base test. -/
theorem completeFiniteSubgroup_baseChange_generator :
    ((H).baseChange g).IsCartierGenerator
      ((H).pullGenerator g (completeFiniteGenerator K n labels hlabels)) :=
  (completeFiniteGenerator_isCartierGenerator K n labels hlabels).baseChange (H) g

/-- Every test retains cyclicity of the original actual subgroup. -/
theorem completeFiniteSubgroup_baseChange_isCyclic : ((H).baseChange g).IsCyclic :=
  (completeFiniteSubgroup_isCyclic K n labels hlabels).baseChange (H) g

/-- Every test retains ampleness of the whole original subgroup divisor. -/
theorem completeFiniteSubgroup_baseChange_isAmple : ((H).baseChange g).IsAmple :=
  (completeFiniteSubgroup_isAmple K n labels hlabels).baseChange g

/-- The closed fiber has exactly the original closed subgroup ideal. -/
theorem completeFiniteSubgroup_closed_ideal :
    ((H).baseChange (c)).ideal = (faithfulClosedCurveMap K n labels hlabels).left.ker := by
  rw [completeFiniteSubgroup_baseChange_ideal, faithfulCompleteIdeal_closed]

end FLT.Mazur.OneGonSmoothing
