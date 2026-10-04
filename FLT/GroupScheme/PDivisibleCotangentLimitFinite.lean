/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentGenerators
public import FLT.GroupScheme.PadicTorsionScalarContinuity
public import FLT.GroupScheme.PDivisibleRationalPlaceTransport

/-! # Finite generation of the original integral cotangent inverse limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Compact p-adic coefficient fibres lift a simultaneous finite-level generating family. -/
theorem cotangentLift_surjective_of_levels (e : R ≃+* ℤ_[p]) {d : ℕ}
    (f : (Fin d → R) →ₗ[R] X.cotangentLimit)
    (hf : ∀ n, Function.Surjective ((X.cotangentEval n).comp f)) : Function.Surjective f := by
  intro x
  let S (n : ℕ) : Set (Fin d → ℤ_[p]) :=
    {c | X.cotangentEval n (f (fun i ↦ e.symm (c i))) = X.cotangentEval n x}
  have hclosed (n : ℕ) : IsClosed (S n) := by
    let : TopologicalSpace (X.LevelCotangent n) := ⊥
    let : DiscreteTopology (X.LevelCotangent n) := ⟨rfl⟩
    exact isClosed_eq
      (continuous_torsion_linearMap e n (X.cotangent_pow_smul_eq_zero n)
        ((X.cotangentEval n).comp f)) continuous_const
  have hnonempty (n : ℕ) : (S n).Nonempty := by
    obtain ⟨c, hc⟩ := hf n (X.cotangentEval n x)
    refine ⟨fun i ↦ e (c i), ?_⟩
    simpa only [S, Set.mem_ofPred_eq, RingEquiv.symm_apply_apply,
      LinearMap.comp_apply] using hc
  have hstep (n : ℕ) : S (n + 1) ⊆ S n := by
    intro c hc
    have he := congrArg (X.cotangentRestriction (Nat.le_succ n)) hc
    simpa only [S, Set.mem_ofPred_eq, X.cotangentEval_restriction] using he
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hstep hnonempty (hclosed 0).isCompact hclosed
  refine ⟨fun i ↦ e.symm (c i), X.cotangentLimit_ext ?_⟩
  exact Set.mem_iInter.mp hc

/-- The actual integral cotangent limit is finite over its original base identified with Z_p. -/
theorem cotangentLimit_finite (e : R ≃+* ℤ_[p]) : Module.Finite R X.cotangentLimit := by
  obtain ⟨d, f, hf⟩ := X.exists_cotangent_level_generators
  exact Module.Finite.of_surjective f (X.cotangentLift_surjective_of_levels e f hf)

end ThreeAdicPlan.PDivisibleSystem
namespace ThreeAdicPlan
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
variable {p height : ℕ} [Fact p.Prime]

/-- Finiteness for the original rational-place system, without replacing its integral levels. -/
theorem rationalPlace_cotangentLimit_finite
    (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height) :
    Module.Finite ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) X.cotangentLimit :=
  X.cotangentLimit_finite (rationalPlaceIntegersEquiv p).toRingEquiv

end ThreeAdicPlan
