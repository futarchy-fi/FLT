/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RamifiedOrderSequence
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral models in an intermediate field

The integral closure in an intermediate field maps into the given integral
closure upstairs. The maps form the actual algebra towers needed for induction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [Algebra S L] [IsFractionRing S L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [IsIntegralClosure S R L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (E : IntermediateField K L)

/-- The intermediate field inclusion commutes with the base ring. -/
instance intermediateDvrScalarTower : IsScalarTower R E L :=
  IsScalarTower.of_algebraMap_eq fun r => ((E.val.restrictScalars R).commutes r).symm

/-- The intermediate integer ring acts on the larger integer ring by its actual inclusion. -/
@[instance_reducible] def intermediateDvrAlgebra : Algebra (integralClosure R E) S :=
  (IsIntegralClosure.lift R S L (S := integralClosure R E)).toRingHom.toAlgebra

attribute [local instance] intermediateDvrAlgebra

/-- This inclusion commutes with the base-ring algebra maps. -/
instance intermediateDvrBaseTower : IsScalarTower R (integralClosure R E) S :=
  IsScalarTower.of_algebraMap_eq fun r =>
    ((IsIntegralClosure.lift R S L (S := integralClosure R E)).commutes r).symm

/-- The inclusion is the original inclusion after passing to fraction fields. -/
instance intermediateDvrFieldTower : IsScalarTower (integralClosure R E) S L :=
  IsScalarTower.of_algebraMap_eq fun x => (IsIntegralClosure.algebraMap_lift R S L x).symm

/-- The intermediate integer ring embeds faithfully in the larger integer ring. -/
instance intermediateDvrFaithful : FaithfulSMul (integralClosure R E) S := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  intro x y h
  apply Subtype.ext
  apply (algebraMap E L).injective
  have h' := congrArg (algebraMap S L) h
  rw [← IsScalarTower.algebraMap_apply (integralClosure R E) S L,
    ← IsScalarTower.algebraMap_apply (integralClosure R E) S L] at h'
  exact h' 

/-- The larger integer ring remains finite over the intermediate one. -/
instance intermediateDvrFinite : Module.Finite (integralClosure R E) S :=
  Module.Finite.of_restrictScalars_finite R (integralClosure R E) S

/-- The upstairs integral closure is also the integral closure over the intermediate integers. -/
instance intermediateDvrIntegralClosure : IsIntegralClosure S (integralClosure R E) L :=
  IsIntegralClosure.tower_top (R := R)

end LocalClassFieldTheory
