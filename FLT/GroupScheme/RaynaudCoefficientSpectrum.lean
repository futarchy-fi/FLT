/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCoefficientTrace
public import FLT.Deformations.RepresentationTheory.RankTwoNonzeroTraceSpectrum

/-!
# Original coefficient-field finite-flat spectrum at a cyclotomic generator

The actual mapped k-linear characteristic polynomial has two nonzero roots
with nonzero sum. Their ratio is not minus one, the obstruction required by
the quadratic self-twist argument. No p±1 ratio classification is asserted.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField Polynomial

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "I" => localInertiaGroup v

/-- The original rank-two coefficient-field action has a nonvanishing spectrum at a generator. -/
theorem coefficient_flat_spectrum {k : Type} [Field k] [CharP k p] (hp : 3 < p)
    (M : FF O Kv) [Module k M.Points] (ρ : Representation k I M.Points)
    (hact : ∀ σ x, ρ σ x = σ • x)
    (hdim : Module.finrank k M.Points = 2)
    (hdet : ∀ σ : I, (ρ σ).det = ZMod.castHom (dvd_refl p) k
      ((LocalRoot.modCyclotomic p σ.1 : (ZMod p)ˣ) : ZMod p)) :
    ∃ σ : I, orderOf (LocalRoot.modCyclotomic p σ.1) = p - 1 ∧
      ∃ a b : (AlgebraicClosure k)ˣ,
        (ρ σ).charpoly.map (algebraMap k (AlgebraicClosure k)) =
          (X - C (a : AlgebraicClosure k)) * (X - C (b : AlgebraicClosure k)) ∧
        (a : AlgebraicClosure k) + (b : AlgebraicClosure k) =
          algebraMap k (AlgebraicClosure k) (LinearMap.trace k M.Points (ρ σ)) ∧
        (a : AlgebraicClosure k) * (b : AlgebraicClosure k) =
          algebraMap k (AlgebraicClosure k) ((ρ σ).det) ∧
        a / b ≠ -1 ∧ LinearMap.trace k M.Points (ρ σ) ≠ 0 := by
  obtain ⟨σ, hσ, ht⟩ := coefficient_flat_trace_ne_zero p M ρ hp hact hdim hdet
  have hd : (ρ σ).det ≠ 0 := by
    rw [hdet]
    exact (_root_.map_ne_zero _).mpr (LocalRoot.modCyclotomic p σ.1).ne_zero
  obtain ⟨a, b, hf, hs, hd, hr⟩ := (ρ σ).exists_map_charpoly_units_of_trace_ne_zero
    (algebraMap k (AlgebraicClosure k)) hdim hd ht
  exact ⟨σ, hσ, a, b, hf, hs, hd, hr, ht⟩

end ThreeAdicPlan
