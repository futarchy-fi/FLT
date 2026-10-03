/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntermediateDvr

/-!
# Canonical integers of a finite subfield

The integral closure construction works for a field embedded in an upstairs local
field, independently of its presentation as an intermediate-field subtype.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K E L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  [Field L] [Algebra R L] [Algebra E L] [Algebra S L]
  [IsScalarTower R E L] [IsScalarTower R S L] [IsFractionRing S L]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The upstairs DVR is the integral closure of the base in its fraction field. -/
theorem finiteSubfieldTopIntegralClosure : IsIntegralClosure S R L :=
  IsIntegralClosure.of_isIntegrallyClosed S R L

include K in
/-- The subfield's canonical integers are finite over the base. -/
theorem finiteSubfieldDvr_finite : Module.Finite R (integralClosure R E) :=
  IsIntegralClosure.finite R K E (integralClosure R E)

include K in
omit [IsDiscreteValuationRing R] [Algebra.IsSeparable K E] in
/-- The subfield is the fraction field of its canonical integers. -/
theorem finiteSubfieldDvr_fractionRing : IsFractionRing (integralClosure R E) E :=
  integralClosure.isFractionRing_of_finite_extension K E

/-- The inclusion of canonical integers into the upstairs DVR. -/
@[instance_reducible] def finiteSubfieldDvrAlgebra : Algebra (integralClosure R E) S := by
  let := finiteSubfieldTopIntegralClosure R S L
  exact (IsIntegralClosure.lift R S L (S := integralClosure R E)).toRingHom.toAlgebra


omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The integer inclusion respects the base ring. -/
theorem finiteSubfieldDvr_baseTower :
    let := finiteSubfieldDvrAlgebra R S E L
    IsScalarTower R (integralClosure R E) S := by
  let := finiteSubfieldDvrAlgebra R S E L
  let := finiteSubfieldTopIntegralClosure R S L
  exact IsScalarTower.of_algebraMap_eq fun r =>
    ((IsIntegralClosure.lift R S L (S := integralClosure R E)).commutes r).symm

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The integer inclusion agrees with the prescribed field inclusion. -/
theorem finiteSubfieldDvr_fieldTower :
    let := finiteSubfieldDvrAlgebra R S E L
    IsScalarTower (integralClosure R E) S L := by
  let := finiteSubfieldDvrAlgebra R S E L
  let := finiteSubfieldTopIntegralClosure R S L
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (IsIntegralClosure.algebraMap_lift R S L x).symm

variable [Algebra (integralClosure R E) S]
  [IsScalarTower R (integralClosure R E) S] [IsScalarTower (integralClosure R E) S L]

include L in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Algebra R L] [IsScalarTower R E L]
  [IsScalarTower R S L] [IsFractionRing S L] [IsScalarTower R (integralClosure R E) S] in
/-- The canonical integers embed faithfully in the upstairs DVR. -/
theorem finiteSubfieldDvr_faithful : FaithfulSMul (integralClosure R E) S := by
  let : FaithfulSMul (integralClosure R E) L :=
    FaithfulSMul.trans (integralClosure R E) E L
  exact FaithfulSMul.tower_bot (integralClosure R E) S L

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S] in
/-- Finiteness upstairs persists over the canonical subfield integers. -/
theorem finiteSubfieldDvr_topFinite : Module.Finite (integralClosure R E) S :=
  Module.Finite.of_restrictScalars_finite R (integralClosure R E) S

variable [Module.Finite (integralClosure R E) S] [FaithfulSMul (integralClosure R E) S]

include S in
omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R S] [Module.Finite R S]
  [IsScalarTower R (integralClosure R E) S] in
/-- Locality descends from the upstairs DVR through the finite integral inclusion. -/
theorem finiteSubfieldDvr_local : IsLocalRing (integralClosure R E) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (algebraMap (integralClosure R E) S a)
  exact h.imp (IsLocalHom.map_nonunit _) (fun h =>
    isUnit_of_map_unit (algebraMap (integralClosure R E) S) _ (by simpa using h))

variable [IsLocalRing (integralClosure R E)]

include K in
/-- The canonical integers are a DVR. -/
theorem finiteSubfieldDvr_discrete : IsDiscreteValuationRing (integralClosure R E) := by
  let : IsDedekindDomain (integralClosure R E) :=
    IsIntegralClosure.isDedekindDomain R K E (integralClosure R E)
  have hf : Function.Injective (algebraMap R (integralClosure R E)) := by
    intro x y h
    apply IsFractionRing.injective R K
    apply (algebraMap K E).injective
    simpa only [← IsScalarTower.algebraMap_apply] using
      congrArg (algebraMap (integralClosure R E) E) h
  have hn : ¬ IsField (integralClosure R E) := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hf h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R E) hn).out 3 1).mp
    (inferInstance : IsDedekindDomain (integralClosure R E))

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R S] [Module.Finite R S]
  [IsScalarTower R (integralClosure R E) S] in
/-- The residue field is finite by its inclusion in the upstairs residue field. -/
theorem finiteSubfieldDvr_residueFinite [Finite (ResidueField S)] :
    Finite (ResidueField (integralClosure R E)) :=
  Finite.of_injective (ResidueField.map (algebraMap (integralClosure R E) S))
    (ResidueField.map (algebraMap (integralClosure R E) S)).injective

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R S] [Module.Finite R S]
  [IsScalarTower R (integralClosure R E) S] in
/-- The residue characteristic is inherited through the same inclusion. -/
theorem finiteSubfieldDvr_residueChar (p : ℕ) [CharP (ResidueField S) p] :
    CharP (ResidueField (integralClosure R E)) p := by
  let f := ResidueField.map (algebraMap (integralClosure R E) S)
  constructor
  intro n
  rw [← CharP.cast_eq_zero_iff (ResidueField S) p n, ← map_natCast f n]
  exact (map_eq_zero_iff f f.injective).symm

include K in
/-- The canonical DVR is complete when the base DVR is complete. -/
theorem finiteSubfieldDvr_complete [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (integralClosure R E)) (integralClosure R E) := by
  let := finiteSubfieldDvr_discrete R K E
  let := finiteSubfieldDvr_finite R K E
  let : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).mpr (by
    rw [IsScalarTower.algebraMap_eq R K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective R K))
  let : FaithfulSMul R (integralClosure R E) :=
    FaithfulSMul.tower_bot R (integralClosure R E) E
  exact finiteDvr_complete R (integralClosure R E)

end LocalClassFieldTheory
