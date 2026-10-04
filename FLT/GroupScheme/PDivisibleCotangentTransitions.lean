/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCotangent
public import FLT.GroupScheme.PDivisibleSystemCategory

/-! # Actual cotangent transition maps of a finite-flat p-divisible system -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Cotangents of the specified integral level, not of a substituted model. -/
abbrev LevelCotangent (n : ℕ) := (X.level n).Cotangent

/-- Closed level inclusions induce the inverse-system cotangent transitions. -/
def cotangentRestriction {m n : ℕ} (h : m ≤ n) :
    X.LevelCotangent n →ₗ[R] X.LevelCotangent m :=
  ModelHom.cotangentMap (X.inclusion h)

/-- Reductions induce the opposite maps on the same original cotangents. -/
def cotangentPullback {m n : ℕ} (h : m ≤ n) :
    X.LevelCotangent m →ₗ[R] X.LevelCotangent n :=
  ModelHom.cotangentMap (X.reduction h)

/-- Every inverse-system transition is surjective. -/
theorem cotangentRestriction_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (X.cotangentRestriction h) :=
  ModelHom.cotangentMap_surjective _ (X.closed h)

/-- Identity inclusions induce identity on cotangents. -/
theorem cotangentRestriction_refl (n : ℕ) :
    X.cotangentRestriction (le_refl n) = LinearMap.id := by
  unfold cotangentRestriction
  rw [X.inclusion_refl, ModelHom.cotangentMap_id]

/-- Identity reductions induce identity on cotangents. -/
theorem cotangentPullback_refl (n : ℕ) :
    X.cotangentPullback (le_refl n) = LinearMap.id := by
  unfold cotangentPullback
  rw [X.reduction_refl, ModelHom.cotangentMap_id]

/-- The actual cotangent inverse-system transitions compose. -/
theorem cotangentRestriction_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (X.cotangentRestriction h).comp (X.cotangentRestriction k) =
      X.cotangentRestriction (h.trans k) := by
  unfold cotangentRestriction
  rw [← ModelHom.cotangentMap_comp, X.inclusion_comp]

/-- The pullbacks compose in the opposite direction. -/
theorem cotangentPullback_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (X.cotangentPullback k).comp (X.cotangentPullback h) =
      X.cotangentPullback (h.trans k) := by
  unfold cotangentPullback
  rw [← ModelHom.cotangentMap_comp, X.reduction_comp]

/-- Restriction after pullback retains the actual multiplication morphism at the lower level. -/
theorem cotangentRestriction_pullback {m n : ℕ} (h : m ≤ n) :
    (X.cotangentRestriction h).comp (X.cotangentPullback h) =
      ModelHom.cotangentMap ((X.level m).multiply (p ^ (n - m))) := by
  unfold cotangentRestriction cotangentPullback
  rw [← ModelHom.cotangentMap_comp, X.inclusion_reduction]

/-- Pullback after restriction retains multiplication at the upper level. -/
theorem cotangentPullback_restriction {m n : ℕ} (h : m ≤ n) :
    (X.cotangentPullback h).comp (X.cotangentRestriction h) =
      ModelHom.cotangentMap ((X.level n).multiply (p ^ (n - m))) := by
  unfold cotangentRestriction cotangentPullback
  rw [← ModelHom.cotangentMap_comp, X.reduction_inclusion]

end ThreeAdicPlan.PDivisibleSystem
