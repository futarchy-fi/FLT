/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateReduction
public import FLT.GroupScheme.PDivisibleTateCompact
public import FLT.Mathlib.RingTheory.NilpotentGeneratorLifting
public import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Finite generation of the original Tate module -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- A family generating the first level generates every original finite level. -/
theorem tateEval_surjective_of_level_one {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (f : M →ₗ[ℤ_[p]] X.tateSequences)
    (hf : Function.Surjective ((X.tateEvalLinear 1).comp f)) (n : ℕ) :
    Function.Surjective ((X.tateEvalLinear n).comp f) := by
  apply LinearMap.surjective_of_scalar_nilpotent _ (p : ℤ_[p]) n
  · intro a
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using X.killed n a
  · intro a
    by_cases hn : 1 ≤ n
    · obtain ⟨b, hb⟩ := hf (genericHom (X.reduction hn) a)
      have hz : genericHom (X.reduction hn) (a - X.tateEval n (f b)) = 0 := by
        rw [map_sub, X.tateEval_reduction]
        exact sub_eq_zero.mpr hb.symm
      obtain ⟨c, hc⟩ := (X.reduction_points_eq_zero_iff hn _).mp hz
      refine ⟨b, c, ?_⟩
      change X.tateEval n (f b) + (p : ℤ_[p]) • c = a
      rw [pow_one] at hc
      rw [Nat.cast_smul_eq_nsmul, hc]
      abel
    · have hn' : n = 0 := by omega
      subst n
      have ha : a = 0 := by simpa using X.killed 0 a
      exact ⟨0, 0, by simp [ha]⟩

/-- A single finite set of actual Tate vectors generates all finite evaluations. -/
theorem exists_tate_level_generators :
    ∃ d : ℕ, ∃ f : (Fin d → ℤ_[p]) →ₗ[ℤ_[p]] X.tateSequences,
      ∀ n, Function.Surjective ((X.tateEvalLinear n).comp f) := by
  let : Module.Finite ℤ_[p] (X.level 1).Points := Module.Finite.of_finite
  obtain ⟨d, g, hg⟩ := Module.Finite.exists_fin' ℤ_[p] (X.level 1).Points
  let b := Pi.basisFun ℤ_[p] (Fin d)
  choose v hv using fun i ↦ X.tateEval_surjective_unconditional 1 (g (b i))
  let f := b.constr ℤ_[p] v
  have he : (X.tateEvalLinear 1).comp f = g := by
    apply b.ext
    intro i
    change X.tateEval 1 (f (b i)) = g (b i)
    simpa only [f, Module.Basis.constr_basis] using hv i
  refine ⟨d, f, X.tateEval_surjective_of_level_one f ?_⟩
  rw [he]
  exact hg

/-- Compact coefficient fibres lift simultaneous finite-level generators to the full limit. -/
theorem tateLift_surjective_of_levels {d : ℕ}
    (f : (Fin d → ℤ_[p]) →ₗ[ℤ_[p]] X.tateSequences)
    (hf : ∀ n, Function.Surjective ((X.tateEvalLinear n).comp f)) : Function.Surjective f := by
  intro x
  let S (n : ℕ) : Set (Fin d → ℤ_[p]) := {c | X.tateEval n (f c) = X.tateEval n x}
  have hclosed (n : ℕ) : IsClosed (S n) := by
    have hcont : Continuous (fun c ↦ X.tateEval n (f c)) := by
      let g := (X.tateEvalLinear n).comp f
      have he (c : Fin d → ℤ_[p]) : g c = ∑ i, c i • g (Pi.single i 1) := by
        conv_lhs => rw [← (Pi.basisFun ℤ_[p] (Fin d)).sum_repr c]
        simp
      have hc : Continuous (fun c : Fin d → ℤ_[p] ↦
          ∑ i, c i • g (Pi.single i 1)) :=
        continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const
      exact hc.congr (fun c ↦ (he c).symm)
    exact isClosed_eq hcont continuous_const
  have hnonempty (n : ℕ) : (S n).Nonempty := hf n (X.tateEval n x)
  have hstep (n : ℕ) : S (n + 1) ⊆ S n := by
    intro c hc
    have he := congrArg (genericHom (X.reduction (Nat.le_succ n))) hc
    simpa only [S, Set.mem_ofPred_eq, X.tateEval_reduction] using he
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hstep hnonempty (hclosed 0).isCompact hclosed
  exact ⟨c, X.tate_ext (Set.mem_iInter.mp hc)⟩

/-- The original Tate module is finite over the p-adic integers. -/
theorem tateSequences_finite : Module.Finite ℤ_[p] X.tateSequences := by
  obtain ⟨d, f, hf⟩ := X.exists_tate_level_generators
  exact Module.Finite.of_surjective f (X.tateLift_surjective_of_levels f hf)
end ThreeAdicPlan.PDivisibleSystem
