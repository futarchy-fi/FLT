/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalComponentClosedPoints
public import FLT.GroupScheme.EtaleClosedImmersion
public import FLT.GroupScheme.RationalEtaleLevelTower

/-! # Closed inclusions of the original étale quotient tower -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]
variable {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)}

/-- A closed immersion descends to a closed immersion of the actual étale quotients. -/
theorem ModelHom.rationalComponentMap_surjective (f : ModelHom X Y)
    (hf : Function.Surjective f) : Function.Surjective f.rationalComponentMap :=
  f.rationalComponentMap.closed_of_etale_target (f.rationalComponentMap_generic_injective hf)

/-- The quotient inclusions are closed over the original integral base, including at p = 2. -/
theorem PDivisibleSystem.rationalEtaleInclusion_closed {height : ℕ}
    (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)
    {m n : ℕ} (h : m ≤ n) : Function.Surjective (X.rationalEtaleInclusion h) :=
  (X.inclusion h).rationalComponentMap_surjective (X.closed h)
end ThreeAdicPlan
