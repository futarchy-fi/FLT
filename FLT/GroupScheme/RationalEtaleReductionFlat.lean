/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleLevelTower
public import Mathlib.RingTheory.Unramified.Finite

/-! # Faithful flatness of the actual étale quotient reductions -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)}

/-- An injective original coordinate map stays injective on contracted quotient coordinates. -/
theorem ModelHom.rationalComponentMap_injective (f : ModelHom X Y)
    (hf : Function.Injective f) : Function.Injective f.rationalComponentMap := by
  intro a b h
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val h

/-- An injective original coordinate map gives a faithfully flat map on the étale quotients. -/
theorem ModelHom.rationalComponentMap_faithfullyFlat (f : ModelHom X Y)
    (hf : Function.Injective f) : f.rationalComponentMap.toAlgHom.toRingHom.FaithfullyFlat := by
  let : Algebra Y.rationalComponentQuotient.CoordinateRing
      X.rationalComponentQuotient.CoordinateRing :=
    f.rationalComponentMap.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower O Y.rationalComponentQuotient.CoordinateRing
      X.rationalComponentQuotient.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' f.rationalComponentMap.toAlgHom.comp_algebraMap.symm
  let : Module.Flat Y.rationalComponentQuotient.CoordinateRing
      X.rationalComponentQuotient.CoordinateRing :=
    Algebra.FormallyUnramified.flat_of_restrictScalars O
      Y.rationalComponentQuotient.CoordinateRing X.rationalComponentQuotient.CoordinateRing
  let : Module.Finite Y.rationalComponentQuotient.CoordinateRing
      X.rationalComponentQuotient.CoordinateRing := Module.Finite.of_restrictScalars_finite O _ _
  let : FaithfulSMul Y.rationalComponentQuotient.CoordinateRing
      X.rationalComponentQuotient.CoordinateRing :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (f.rationalComponentMap_injective hf)
  exact Module.FaithfullyFlat.of_comap_surjective (Algebra.IsIntegral.comap_surjective _ _)

/-- Every actual reduction on the étale quotient tower is faithfully flat. -/
theorem PDivisibleSystem.rationalEtaleReduction_faithfullyFlat {height : ℕ}
    (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)
    {m n : ℕ} (h : m ≤ n) :
    (X.rationalEtaleReduction h).toAlgHom.toRingHom.FaithfullyFlat :=
  (X.reduction h).rationalComponentMap_faithfullyFlat (X.faithfullyFlat h).injective
end ThreeAdicPlan
