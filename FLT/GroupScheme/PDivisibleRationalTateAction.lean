/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleRationalPlaceTransport
public import FLT.GroupScheme.PDivisibleTateTopology

/-! # The standard p-adic Galois action on the original Tate sequences -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
open PadicHodgeTheory
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Transport only the acting group; retain the original integral Tate module. -/
def rationalTateAction : PadicGalois p →* X.tateSequences ≃ₗ[ℤ_[p]] X.tateSequences :=
  (DistribMulAction.toModuleAut ℤ_[p] X.tateSequences).comp
    (rationalPlaceGaloisEquiv p).symm.toMonoidHom

/-- This action uses the original rational-place automorphism at each level. -/
theorem rationalTateAction_eval (σ : PadicGalois p) (x : X.tateSequences) (n : ℕ) :
    X.tateEval n (X.rationalTateAction σ x) =
      (rationalPlaceGaloisEquiv p).symm σ • X.tateEval n x := rfl

/-- The change of Galois coordinates agrees exactly with the original Tate action. -/
theorem rationalTateAction_original
    (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
    (x : X.tateSequences) :
    X.rationalTateAction (rationalPlaceGaloisEquiv p σ) x = σ • x := by
  change (rationalPlaceGaloisEquiv p).symm (rationalPlaceGaloisEquiv p σ) • x = _
  rw [MulEquiv.symm_apply_apply]

/-- The transported action is jointly continuous on the original topological Tate module. -/
theorem rationalTateAction_continuous :
    Continuous (fun z : PadicGalois p × X.tateSequences ↦ X.rationalTateAction z.1 z.2) :=
  ((rationalPlaceGaloisContinuousEquiv p).symm.continuous.comp continuous_fst).smul
    continuous_snd

/-- Fixed sequences are unchanged by the actual Galois identification. -/
theorem rationalTateAction_fixed_iff (x : X.tateSequences) :
    (∀ σ : PadicGalois p, X.rationalTateAction σ x = x) ↔
    ∀ σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ),
      σ • x = x := by
  constructor
  · intro hx σ
    simpa only [X.rationalTateAction_original] using hx (rationalPlaceGaloisEquiv p σ)
  · intro hx σ
    exact hx ((rationalPlaceGaloisEquiv p).symm σ)

/-- Transported evaluation remains compatible with the actual integral reductions. -/
theorem rationalTateAction_reduction (σ : PadicGalois p) (x : X.tateSequences)
    {m n : ℕ} (h : m ≤ n) :
    genericHom (X.reduction h) (X.tateEval n (X.rationalTateAction σ x)) =
      X.tateEval m (X.rationalTateAction σ x) :=
  X.tateEval_reduction h _

end ThreeAdicPlan.PDivisibleSystem
