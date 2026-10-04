/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalComponentMaps
public import FLT.GroupScheme.RationalComponentQuotientEtale
public import FLT.GroupScheme.PDivisibleSystem

/-! # Étale quotient levels and coherent original transitions

These are the actual finite étale quotient levels. Closed inclusions and kernel
exactness remain separate obligations before bundling a quotient p-divisible system.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem
  ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The actual étale quotient component at each original level. -/
abbrev rationalEtaleLevel (n : ℕ) : FF O K := (X.level n).rationalComponentQuotient

/-- The original inclusions descend to the étale quotient levels. -/
def rationalEtaleInclusion {m n : ℕ} (h : m ≤ n) :
    ModelHom (X.rationalEtaleLevel m) (X.rationalEtaleLevel n) :=
  (X.inclusion h).rationalComponentMap

/-- The original reductions descend to the étale quotient levels. -/
def rationalEtaleReduction {m n : ℕ} (h : m ≤ n) :
    ModelHom (X.rationalEtaleLevel n) (X.rationalEtaleLevel m) :=
  (X.reduction h).rationalComponentMap

/-- The projection from the original level to its actual étale quotient. -/
abbrev rationalEtaleProjection (n : ℕ) : ModelHom (X.level n) (X.rationalEtaleLevel n) :=
  (X.level n).rationalComponentProjection

/-- The original inclusions commute with the quotient projections. -/
theorem rationalEtaleInclusion_naturality {m n : ℕ} (h : m ≤ n) :
    (X.rationalEtaleProjection m).comp (X.rationalEtaleInclusion h) =
      (X.inclusion h).comp (X.rationalEtaleProjection n) :=
  (X.inclusion h).rationalComponentMap_naturality

/-- The original reductions commute with the quotient projections. -/
theorem rationalEtaleReduction_naturality {m n : ℕ} (h : m ≤ n) :
    (X.rationalEtaleProjection n).comp (X.rationalEtaleReduction h) =
      (X.reduction h).comp (X.rationalEtaleProjection m) :=
  (X.reduction h).rationalComponentMap_naturality

/-- Étale quotient inclusions preserve identity levels. -/
theorem rationalEtaleInclusion_refl (n : ℕ) :
    X.rationalEtaleInclusion (le_refl n) = BialgHom.id O _ := by
  rw [rationalEtaleInclusion, X.inclusion_refl, ModelHom.rationalComponentMap_id]

/-- Étale quotient reductions preserve identity levels. -/
theorem rationalEtaleReduction_refl (n : ℕ) :
    X.rationalEtaleReduction (le_refl n) = BialgHom.id O _ := by
  rw [rationalEtaleReduction, X.reduction_refl, ModelHom.rationalComponentMap_id]

/-- Étale quotient inclusions obey all original coherence relations. -/
theorem rationalEtaleInclusion_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (X.rationalEtaleInclusion h).comp (X.rationalEtaleInclusion k) =
      X.rationalEtaleInclusion (h.trans k) := by
  rw [rationalEtaleInclusion, rationalEtaleInclusion, rationalEtaleInclusion,
    ← ModelHom.rationalComponentMap_comp, X.inclusion_comp]

/-- Étale quotient reductions obey all original coherence relations. -/
theorem rationalEtaleReduction_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (X.rationalEtaleReduction k).comp (X.rationalEtaleReduction h) =
      X.rationalEtaleReduction (h.trans k) := by
  rw [rationalEtaleReduction, rationalEtaleReduction, rationalEtaleReduction,
    ← ModelHom.rationalComponentMap_comp, X.reduction_comp]

/-- The étale quotient retains the original p-power annihilator. -/
theorem rationalEtaleLevel_killed (n : ℕ) (x : (X.rationalEtaleLevel n).Points) :
    p ^ n • x = 0 := by
  obtain ⟨y, rfl⟩ := (X.level n).rationalComponentGenericProjection_surjective x
  change p ^ n • (X.level n).rationalComponentGenericProjection y =
    (0 : (X.level n).rationalComponentQuotientWitness.Points)
  rw [← map_nsmul, X.killed, map_zero]

/-- The lower étale quotient multiplication factors through the original restricted transitions. -/
theorem rationalEtaleInclusion_reduction {m n : ℕ} (h : m ≤ n) :
    (X.rationalEtaleInclusion h).comp (X.rationalEtaleReduction h) =
      (X.rationalEtaleLevel m).multiply (p ^ (n - m)) := by
  rw [rationalEtaleInclusion, rationalEtaleReduction,
    ← ModelHom.rationalComponentMap_comp, X.inclusion_reduction,
    ModelHom.rationalComponentMap_multiply]

/-- The higher étale quotient multiplication factors through the original restricted transitions. -/
theorem rationalEtaleReduction_inclusion {m n : ℕ} (h : m ≤ n) :
    (X.rationalEtaleReduction h).comp (X.rationalEtaleInclusion h) =
      (X.rationalEtaleLevel n).multiply (p ^ (n - m)) := by
  rw [rationalEtaleInclusion, rationalEtaleReduction,
    ← ModelHom.rationalComponentMap_comp, X.reduction_inclusion,
    ModelHom.rationalComponentMap_multiply]

end ThreeAdicPlan.PDivisibleSystem
