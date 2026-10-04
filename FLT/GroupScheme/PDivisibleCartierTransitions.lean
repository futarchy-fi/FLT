/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierArithmetic
public import FLT.GroupScheme.PDivisibleSystem

/-! # Coherence and multiplication for the transposed original transitions -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- The dual inclusion is the original reduction's transpose. -/
def dualInclusion {m n : ℕ} (h : m ≤ n) :
    ModelHom (X.level m).cartierDual (X.level n).cartierDual := (X.reduction h).cartierDual

/-- The dual reduction is the original inclusion's transpose. -/
def dualReduction {m n : ℕ} (h : m ≤ n) :
    ModelHom (X.level n).cartierDual (X.level m).cartierDual := (X.inclusion h).cartierDual

/-- Transposed inclusions are identities at equal levels. -/
theorem dualInclusion_refl (n : ℕ) :
    X.dualInclusion (le_refl n) = BialgHom.id R (X.level n).cartierDual.CoordinateRing := by
  simp only [dualInclusion, X.reduction_refl, ModelHom.cartierDual,
    HopfAlgebra.CartierDual.bialgMap_id]
  rfl

/-- Transposed reductions are identities at equal levels. -/
theorem dualReduction_refl (n : ℕ) :
    X.dualReduction (le_refl n) = BialgHom.id R (X.level n).cartierDual.CoordinateRing := by
  simp only [dualReduction, X.inclusion_refl, ModelHom.cartierDual,
    HopfAlgebra.CartierDual.bialgMap_id]
  rfl

/-- Original reduction coherence gives dual inclusion coherence. -/
theorem dualInclusion_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (X.dualInclusion h).comp (X.dualInclusion k) = X.dualInclusion (h.trans k) := by
  simp only [dualInclusion, ← ModelHom.cartierDual_comp, X.reduction_comp]

/-- Original inclusion coherence gives dual reduction coherence. -/
theorem dualReduction_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (X.dualReduction k).comp (X.dualReduction h) = X.dualReduction (h.trans k) := by
  simp only [dualReduction, ← ModelHom.cartierDual_comp, X.inclusion_comp]

/-- Multiplication factors through the transposed maps on the smaller level. -/
theorem dualInclusion_reduction {m n : ℕ} (h : m ≤ n) :
    (X.dualInclusion h).comp (X.dualReduction h) =
      (X.level m).cartierDual.multiply (p ^ (n - m)) := by
  simp only [dualInclusion, dualReduction, ← ModelHom.cartierDual_comp,
    X.inclusion_reduction, FF.cartierDual_multiply]

/-- Multiplication factors through the transposed maps on the larger level. -/
theorem dualReduction_inclusion {m n : ℕ} (h : m ≤ n) :
    (X.dualReduction h).comp (X.dualInclusion h) =
      (X.level n).cartierDual.multiply (p ^ (n - m)) := by
  simp only [dualInclusion, dualReduction, ← ModelHom.cartierDual_comp,
    X.reduction_inclusion, FF.cartierDual_multiply]

end ThreeAdicPlan.PDivisibleSystem
