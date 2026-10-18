/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEmbeddingExchangeInvariance

/-!
# One crossing exchange generates all missing invariance equations

The setwise stabilizer of a selected image transports any chosen crossing swap
to every other crossing swap. Thus one exchange, together with the already
available setwise invariance, suffices for the entire permutation action.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteEmbeddingExchangeInvariance
open Equiv
variable {I J M : Type*} [DecidableEq I] [MulAction (Perm I) M]

/-- Transport one crossing exchange using only internal and external label permutations. -/
theorem crossing_swaps_of_one (ι : J ↪ I) (x : M)
    (hr : ∀ σ : Perm I,
      Set.range (ι.trans σ.toEmbedding : J → I) = Set.range ι → σ • x = x)
    (a₀ b₀ : I) (ha₀ : a₀ ∈ Set.range ι) (hb₀ : b₀ ∉ Set.range ι)
    (hs : swap a₀ b₀ • x = x) :
    ∀ a ∈ Set.range ι, ∀ b ∉ Set.range ι, swap a b • x = x := by
  intro a ha b hb
  let τ : Perm I := swap a₀ a * swap b₀ b
  have hτ : τ • x = x := by
    change (swap a₀ a * swap b₀ b) • x = x
    rw [mul_smul, hr _ (range_swap_eq ι b₀ b (iff_of_false hb₀ hb)),
      hr _ (range_swap_eq ι a₀ a (iff_of_true ha₀ ha))]
  have hτa : τ a₀ = a := by
    change swap a₀ a (swap b₀ b a₀) = a
    rw [swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem ha₀ hb₀)
      (ne_of_mem_of_not_mem ha₀ hb), swap_apply_left]
  have hτb : τ b₀ = b := by
    change swap a₀ a (swap b₀ b b₀) = b
    rw [swap_apply_left, swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem ha₀ hb).symm
      (ne_of_mem_of_not_mem ha hb).symm]
  have he := congrArg (fun σ : Perm I ↦ σ • x) (mul_swap_eq_swap_mul τ a₀ b₀)
  rw [mul_smul, hs, hτ, mul_smul, hτ, hτa, hτb] at he
  exact he.symm

variable [Finite I]

/-- One selected-to-omitted swap detects full invariance once setwise invariance is known. -/
theorem fixed_iff_one_crossing_swap (ι : J ↪ I) (x : M)
    (hr : ∀ σ : Perm I,
      Set.range (ι.trans σ.toEmbedding : J → I) = Set.range ι → σ • x = x)
    (a₀ b₀ : I) (ha₀ : a₀ ∈ Set.range ι) (hb₀ : b₀ ∉ Set.range ι) :
    (∀ σ : Perm I, σ • x = x) ↔ swap a₀ b₀ • x = x := by
  refine ⟨fun h ↦ h _, fun hs ↦ fixed_of_crossing_swaps ι x hr ?_⟩
  exact crossing_swaps_of_one ι x hr a₀ b₀ ha₀ hb₀ hs

end FLT.Mazur.FiniteEmbeddingExchangeInvariance
