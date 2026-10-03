/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedContinuousOrderSequence
public import FLT.LocalClassFieldTheory.ContinuousColimitNaturality

/-!
# Continuous order isomorphisms

The long exact sequence and proved continuous unit acyclicity make the
actual order coefficient map an isomorphism on every positive cohomology group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory Limits HomologicalComplex

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C
local notation "G" => Gal(U/K)
local notation "ord" => unramifiedUnionOrderMap R K C

attribute [local instance] unramifiedUnionGalois integralUnitAction fieldUnitAction
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous
  unramifiedUnitTopology unramifiedUnitDiscrete
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete

/-- Positive continuous cohomology is unchanged by applying normalized order. -/
theorem unramifiedContinuousOrder_isIso (i : ℕ) :
    IsIso (continuousCoefficientCohomologyMap ord (i + 1)) := by
  let S := unramifiedContinuousOrderSequence R K C
  have hS := unramifiedContinuousOrderSequence_shortExact R K C
  have hz := unramifiedContinuousUnitCohomology_isZero R K C i
  have hz' := unramifiedContinuousUnitCohomology_isZero R K C (i + 1)
  have h₂ := hS.homology_exact₂ (i + 1)
  have h₃ := hS.homology_exact₃ (i + 1) (i + 2) rfl
  let : Mono (homologyMap S.g (i + 1)) :=
    h₂.mono_g (hz.eq_zero_of_src _)
  let : Epi (homologyMap S.g (i + 1)) :=
    h₃.epi_f (hz'.eq_zero_of_tgt _)
  change IsIso (homologyMap S.g (i + 1))
  exact isIso_of_mono_of_epi _

/-- The continuous multiplicative H2 comparison induced by normalized integer order. -/
def unramifiedContinuousOrderH2Iso :
    continuousCohomology ℤ G (Additive Uˣ) 2 ≅ continuousCohomology ℤ G ℤ 2 :=
  @asIso (ModuleCat ℤ) _ _ _ (continuousCoefficientCohomologyMap ord 2)
    (unramifiedContinuousOrder_isIso R K C 1)

/-- The order comparison commutes with the genuine invariant-stage colimit comparison. -/
theorem unramifiedContinuousOrder_colimit (i : ℕ) :
    colimMap (invariantStageCohomologyCoefficientNat ord i) ≫
        (continuousCohomologyColimitIso ℤ G ℤ i).hom =
      (continuousCohomologyColimitIso ℤ G (Additive Uˣ) i).hom ≫
        continuousCoefficientCohomologyMap ord i :=
  continuousCohomologyColimitIso_naturality ord i

end LocalClassFieldTheory
