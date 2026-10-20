/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleRingTower
public import FLT.Mazur.HomogeneousNumeratorObstruction

/-!
# Exact all-order numerator obstruction

The obstruction lives over the ring of compatible global coefficients.
A power kills it exactly when a single exponent has homogeneous global
numerators compatible at every pair of orders. Stagewise numerator existence
is only a necessary condition for this all-order assertion.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.CompatibleRingTower
variable {R S : ℕ → Type*} [∀ k, CommRing (R k)] [∀ k, CommRing (S k)]
  (ρ : ∀ k l, k ≤ l → R l →+* R k)
  (σ : ∀ k l, k ≤ l → S l →+* S k) (f : ∀ k, R k →+* S k)
  (hsq : ∀ k l (h : k ≤ l) z, f k (ρ k l h z) = σ k l h (f l z))
  (I : ∀ k, Ideal (R k)) (x : ring σ)

/-- The scalar ideal uses the image of the entire compatible homogeneous source. -/
def numeratorIdeal : Ideal (ring ρ) :=
  HomogeneousNumeratorObstruction.scalarIdeal (map ρ σ f hsq) (ideal ρ I) x

/-- Admissibility retains all orders and all full homogeneous ideal conditions. -/
theorem mem_numeratorIdeal (a : ring ρ) :
    a ∈ numeratorIdeal ρ σ f hsq I x ↔
      ∃ w : ∀ k, R k, (∀ k, w k ∈ I k) ∧
        (∀ k l (h : k ≤ l), ρ k l h (w l) = w k) ∧
        ∀ k, f k (w k) = f k (a.val k) * x.val k := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact ⟨w.val, hw, w.property, fun k ↦ congrArg (fun z : ring σ ↦ z.val k) he⟩
  · rintro ⟨w, hw, ht, he⟩
    exact ⟨⟨w, ht⟩, hw, Subtype.ext (funext he)⟩

/-- Radical membership is a genuinely order-uniform exponent with coherent numerators. -/
theorem mem_radical_numeratorIdeal (r : ring ρ) :
    r ∈ (numeratorIdeal ρ σ f hsq I x).radical ↔
      ∃ (N : ℕ) (w : ∀ k, R k), (∀ k, w k ∈ I k) ∧
        (∀ k l (h : k ≤ l), ρ k l h (w l) = w k) ∧
        ∀ k, f k (w k) = f k (r.val k) ^ N * x.val k := by
  simp only [Ideal.mem_radical_iff, mem_numeratorIdeal, Subring.coe_pow,
    Pi.pow_apply, map_pow]

/-- Evaluation of a coherent numerator is a numerator in every stage scalar ideal. -/
theorem numeratorIdeal_le_stage (k : ℕ) :
    numeratorIdeal ρ σ f hsq I x ≤
      Ideal.comap (eval ρ k)
        (HomogeneousNumeratorObstruction.scalarIdeal (f k) (I k) (x.val k)) := by
  intro a ha
  obtain ⟨w, hw, _, he⟩ := (mem_numeratorIdeal ρ σ f hsq I x a).mp ha
  exact ⟨w k, hw k, he k⟩

/-- The all-order scalar obstruction is cyclic; this does not assert it vanishes. -/
theorem numeratorQuotient_finite :
    Module.Finite (ring ρ) ((ring ρ) ⧸ numeratorIdeal ρ σ f hsq I x) := inferInstance

end FLT.Mazur.CompatibleRingTower
