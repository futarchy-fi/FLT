/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntermediateDvrAlgebra
public import FLT.LocalClassFieldTheory.FiniteDvrComplete

/-!
# The complete DVR of an intermediate field

Finiteness and integral inclusion in the upstairs DVR prove locality of the
intermediate integral closure. Dedekindness and nonfieldness give a DVR;
finite-extension completeness then supplies its own adic completeness.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [Algebra S L] [IsFractionRing S L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [IsIntegralClosure S R L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (E : IntermediateField K L)

attribute [local instance] intermediateDvrAlgebra

/-- The intermediate integral closure is finite over the original DVR. -/
instance intermediateDvrBaseFinite : Module.Finite R (integralClosure R E) :=
  IsIntegralClosure.finite R K E (integralClosure R E)

/-- Its fraction field is the intermediate field itself. -/
instance intermediateDvrFractionRing : IsFractionRing (integralClosure R E) E :=
  integralClosure.isFractionRing_of_finite_extension K E

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsFractionRing S L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] in
include S in
/-- Locality descends along the finite integral inclusion into the upstairs DVR. -/
theorem intermediateDvrLocal : IsLocalRing (integralClosure R E) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  have h := IsLocalRing.isUnit_or_isUnit_one_sub_self
    (algebraMap (integralClosure R E) S a)
  exact h.imp (IsLocalHom.map_nonunit _) (fun h =>
    isUnit_of_map_unit (algebraMap (integralClosure R E) S) _ (by simpa using h))

/-- Faithfulness of the base action follows from the fraction-field inclusion. -/
instance intermediateDvrBaseFaithful : FaithfulSMul R (integralClosure R E) := by
  let : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).mpr (by
    rw [IsScalarTower.algebraMap_eq R K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective R K))
  exact FaithfulSMul.tower_bot R (integralClosure R E) E

variable [IsLocalRing (integralClosure R E)]

/-- The intermediate integral closure is a DVR, with no unramifiedness premise. -/
instance intermediateDvr : IsDiscreteValuationRing (integralClosure R E) := by
  let : IsDedekindDomain (integralClosure R E) :=
    IsIntegralClosure.isDedekindDomain R K E (integralClosure R E)
  have hn : ¬ IsField (integralClosure R E) := fun h =>
    IsDiscreteValuationRing.not_isField R
      (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective R _) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R E) hn).out 3 1).mp
    (inferInstance : IsDedekindDomain (integralClosure R E))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsFractionRing S L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The intermediate residue field is finite by its injection into the upstairs residue field. -/
theorem intermediateDvrResidueFinite [Finite (ResidueField S)] :
    Finite (ResidueField (integralClosure R E)) :=
  Finite.of_injective (ResidueField.map (algebraMap (integralClosure R E) S))
    (ResidueField.map (algebraMap (integralClosure R E) S)).injective

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsFractionRing S L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The intermediate residue characteristic is inherited through that injection. -/
theorem intermediateDvrResidueChar (p : ℕ) [CharP (ResidueField S) p] :
    CharP (ResidueField (integralClosure R E)) p := by
  let f := ResidueField.map (algebraMap (integralClosure R E) S)
  constructor
  intro n
  rw [← CharP.cast_eq_zero_iff (ResidueField S) p n, ← map_natCast f n]
  exact (map_eq_zero_iff f f.injective).symm

/-- The intermediate DVR is complete over a complete original DVR. -/
instance intermediateDvrComplete [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (integralClosure R E)) (integralClosure R E) :=
  finiteDvr_complete R (integralClosure R E)

end LocalClassFieldTheory
