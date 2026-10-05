/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalCyclotomicRootVector
public import FLT.GroupScheme.PDivisibleTateCompact

/-! # The prescribed cyclotomic vector is an integral basis -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- Compact coefficient fibres give one scalar realizing all prescribed root coordinates. -/
theorem rationalCyclotomicRootLinear_surjective :
    Function.Surjective (rationalCyclotomicRootLinear p) := by
  intro x
  let S (n : ℕ) : Set ℤ_[p] := {a | tateRootEval (AlgebraicClosure K) p n
    (rationalCyclotomicRootLinear p a) = tateRootEval (AlgebraicClosure K) p n x}
  have hclosed (n : ℕ) : IsClosed (S n) := by
    let : TopologicalSpace (TateRootLevel (AlgebraicClosure K) p n) := ⊥
    let : DiscreteTopology (TateRootLevel (AlgebraicClosure K) p n) := ⟨rfl⟩
    have hc : Continuous (fun a : ℤ_[p] ↦ tateRootEval (AlgebraicClosure K) p n
        (rationalCyclotomicRootLinear p a)) := by
      change Continuous (fun a : ℤ_[p] ↦ PadicInt.toZModPow n a •
        tateRootEval (AlgebraicClosure K) p n (rationalCyclotomicRootVector p))
      exact (continuous_of_discreteTopology (f := fun a : ZMod (p ^ n) ↦ a •
        tateRootEval (AlgebraicClosure K) p n (rationalCyclotomicRootVector p))).comp
          (PDivisibleSystem.continuous_padicResidue (p := p) n)
    exact isClosed_eq hc continuous_const
  have hnonempty (n : ℕ) : (S n).Nonempty :=
    rationalCyclotomicRootLinear_level_surjective p n (tateRootEval (AlgebraicClosure K) p n x)
  have hstep (n : ℕ) : S (n + 1) ⊆ S n := by
    intro a ha
    have h := congrArg (tateRootReduction (AlgebraicClosure K) p (Nat.le_succ n)) ha
    exact ((rationalCyclotomicRootLinear p a).property (Nat.le_succ n)).symm.trans
      (h.trans (x.property (Nat.le_succ n)))
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hstep hnonempty (hclosed 0).isCompact hclosed
  refine ⟨a, ?_⟩
  apply Subtype.ext
  funext n
  exact Set.mem_iInter.mp ha n

/-- The integral root module is Z_p with one sent to the prescribed primitive sequence. -/
def rationalCyclotomicRootEquiv : ℤ_[p] ≃ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p :=
  LinearEquiv.ofBijective (rationalCyclotomicRootLinear p)
    ⟨rationalCyclotomicRootLinear_injective p, rationalCyclotomicRootLinear_surjective p⟩

/-- This identification uses the fixed original roots, without an arbitrary basis choice. -/
theorem rationalCyclotomicRootEquiv_one :
    rationalCyclotomicRootEquiv p 1 = rationalCyclotomicRootVector p := by
  change (1 : ℤ_[p]) • rationalCyclotomicRootVector p = _
  exact one_smul _ _
end ThreeAdicPlan
