/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOrderCohomology
public import FLT.LocalClassFieldTheory.UnramifiedStageFrobenius

/-!
# Order and unit acyclicity for the constructed unramified stages

The arithmetic results apply to the canonical integral closures in the existing
degree-indexed diagram. All DVR, finiteness, freeness, localness and unramifiedness
instances are derived from the constructed stages.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory Limits IsLocalRing

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "E[" n "]" => unramifiedFiniteStage R K C n
local notation "S[" n "]" => integralClosure R (E[n])

attribute [local instance] stageDvr stageUnramified stageFractionRing stageFinite stageLocalHom

/-- The actual canonical integral model is finite free over the base DVR. -/
local instance canonicalStageFree (n : UnramifiedIndex) : Module.Free R (S[n]) := by
  have : Module.IsTorsionFree R (E[n]) := .trans_faithfulSMul R K (E[n])
  exact IsIntegralClosure.module_free R K (E[n]) (S[n])

/-- The unit norm is surjective at every constructed unramified stage. -/
theorem unramifiedFiniteStage_unit_norm_surjective (n : UnramifiedIndex) :
    Function.Surjective (Units.map (Algebra.norm R) : (S[n])ˣ →* Rˣ) :=
  unramified_unit_norm_surjective R (S[n])

/-- The integral units of every constructed stage have zero positive cohomology. -/
theorem unramifiedFiniteStage_unit_cohomology_isZero (n : UnramifiedIndex) (i : ℕ) :
    IsZero (groupCohomology (integralUnitRep R (S[n]) K (E[n])) (i + 1)) :=
  unramified_unit_cohomology_isZero R (S[n]) K (E[n]) i

/-- Order gives the actual degree-two isomorphism at each stage of the unramified diagram. -/
def unramifiedStageOrderH2Iso (n : UnramifiedIndex) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K (E[n])) 2 ≅
      groupCohomology (Rep.trivial ℤ Gal(E[n]/K) ℤ) 2 :=
  unramifiedOrderH2Iso R (S[n]) K (E[n])

end LocalClassFieldTheory
