/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicTower
public import FLT.PadicHodgeTheory.NormalizedTraceTower

/-! # Actual normalized trace projections onto cyclotomic levels

These are the algebraic normalized traces. No uniform norm bound or extension
to the completion is asserted here.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The original algebraic closure is integral over each cyclotomic level. -/
instance instIntegralPadicCyclotomicTower (n : ℕ) :
    Algebra.IsIntegral (padicCyclotomicTower p n) (PadicAlgCl p) :=
  ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) x).tower_top⟩

/-- Normalize the actual field trace onto the nth cyclotomic subfield. -/
def padicCyclotomicTrace (n : ℕ) : PadicAlgCl p →ₗ[padicCyclotomicTower p n]
    padicCyclotomicTower p n := Algebra.normalizedTrace _ _

/-- Regard the actual trace as an endomorphism of the original Q_p-vector space. -/
def padicCyclotomicProjection (n : ℕ) : PadicAlgCl p →ₗ[ℚ_[p]] PadicAlgCl p :=
  (padicCyclotomicTower p n).val.toLinearMap ∘ₗ (padicCyclotomicTrace p n).restrictScalars ℚ_[p]

/-- Projection is the original field embedding of the normalized trace. -/
theorem padicCyclotomicProjection_apply (n : ℕ) (x : PadicAlgCl p) :
    padicCyclotomicProjection p n x = (padicCyclotomicTrace p n x : PadicAlgCl p) := rfl

/-- The trace fixes every element already in its target field. -/
theorem padicCyclotomicTrace_coe (n : ℕ) (x : padicCyclotomicTower p n) :
    padicCyclotomicTrace p n (x : PadicAlgCl p) = x := by
  change Algebra.normalizedTrace (padicCyclotomicTower p n) (PadicAlgCl p)
    (algebraMap (padicCyclotomicTower p n) (PadicAlgCl p) x) = x
  rw [Algebra.normalizedTrace_algebraMap_apply, Algebra.normalizedTrace_self_apply]

/-- The actual normalized trace is an idempotent projection. -/
theorem padicCyclotomicProjection_idempotent (n : ℕ) (x : PadicAlgCl p) :
    padicCyclotomicProjection p n (padicCyclotomicProjection p n x) =
      padicCyclotomicProjection p n x := by
  simp only [padicCyclotomicProjection_apply, padicCyclotomicTrace_coe]

/-- On a finite extension, this is the usual trace divided by the actual field degree. -/
theorem padicCyclotomicTrace_finite (n : ℕ)
    (E : IntermediateField (padicCyclotomicTower p n) (PadicAlgCl p))
    [FiniteDimensional (padicCyclotomicTower p n) E] (x : E) :
    padicCyclotomicTrace p n (x : PadicAlgCl p) =
      (Module.finrank (padicCyclotomicTower p n) E : padicCyclotomicTower p n)⁻¹ *
        Algebra.trace (padicCyclotomicTower p n) E x := by
  change Algebra.normalizedTrace _ _ (x : PadicAlgCl p) = _
  rw [Algebra.normalizedTrace_intermediateField,
    Algebra.normalizedTrace_eq_of_finiteDimensional_apply, smul_eq_mul]

/-- Nested cyclotomic projections compose to the lower-level projection. -/
theorem padicCyclotomicProjection_trans {n m : ℕ} (h : n ≤ m) (x : PadicAlgCl p) :
    padicCyclotomicProjection p n (padicCyclotomicProjection p m x) =
      padicCyclotomicProjection p n x := by
  exact normalizedTrace_nested_projection ℚ_[p] (PadicAlgCl p)
    (padicCyclotomicTower p n) (padicCyclotomicTower p m)
    (padicCyclotomicTower_mono p h) x

end PadicHodgeTheory
