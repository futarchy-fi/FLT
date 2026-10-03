/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisKernelTopology
public import FLT.LocalClassFieldTheory.KernelSectionCorrection

/-!
# Finite Galois kernel cocycle correction

Subtract a restricted bounding cochain, then use Hilbert 90 on the mixed
crossed homomorphisms. The resulting representative vanishes whenever
either argument belongs to the restriction kernel.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology GaloisRepresentation.Extensions

/-- Assemble principal mixed witnesses into one correcting cochain. -/
theorem exists_mixed_zero_twoCocycle {G H M : Type*} [Group G] [Group H]
    [AddCommGroup M] [DistribMulAction G M] (f : G →* H) (hf : Function.Surjective f)
    (c : G × G → M) (hc : IsCocycle₂ c) (hN : ∀ n m : f.ker, c (n, m) = 0)
    (hm : ∀ g, ∃ a : M, ∀ n, kernelMixedCocycle f c g n = (n : G) • a - a) :
    ∃ b : G → M, (∀ n : f.ker, b n = 0) ∧
      (∀ n : f.ker, ∀ g, correctTwoCocycle c b (n, g) = 0) ∧
      (∀ g, ∀ n : f.ker, correctTwoCocycle c b (g, n) = 0) := by
  classical
  obtain ⟨s, hs, hs1⟩ := exists_normalized_section f hf
  let a : H → M := fun q => if q = 1 then 0 else (hm (s q)).choose
  have ha1 : a 1 = 0 := by simp [a]
  have ha : ∀ q n, kernelMixedCocycle f c (s q) n = (n : G) • a q - a q := by
    intro q n
    by_cases h : q = 1
    · simp [h, hs1, kernelMixedCocycle_one f c hc hN, ha1]
    · simpa only [a, ite_eq_right h] using (hm (s q)).choose_spec n
  exact ⟨sectionCorrection f s hs c a,
    sectionCorrection_kernel f s hs hs1 c hc hN a ha1,
    sectionCorrection_zero_left f s hs hs1 c hc hN a ha1,
    sectionCorrection_zero_right f s hs hs1 c hc hN a ha1 ha⟩

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [FiniteDimensional K L] (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "res" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

/-- Hilbert 90 supplies the mixed-term correction in a finite Galois tower. -/
theorem finiteKernelCocycleCorrection (c : Gal(L/K) × Gal(L/K) → Additive Lˣ)
    (hc : IsCocycle₂ c) (b : (res).ker → Additive Lˣ)
    (hb : ∀ n m : (res).ker, c (n, m) = n • b m - b (n * m) + b n) :
    ∃ a : Gal(L/K) → Additive Lˣ, IsCocycle₂ (correctTwoCocycle c a) ∧
      (∀ n : (res).ker, ∀ g, correctTwoCocycle c a (n, g) = 0) ∧
      (∀ g, ∀ n : (res).ker, correctTwoCocycle c a (g, n) = 0) := by
  obtain ⟨a, ha, hN⟩ := exists_kernel_zero_twoCocycle (res).ker c hc b hb
  let d := correctTwoCocycle c a
  have hm (g : Gal(L/K)) : ∃ u : Additive Lˣ,
      ∀ n, kernelMixedCocycle res d g n = (n : Gal(L/K)) • u - u := by
    let z : ContinuousCocycle (res).ker (Additive Lˣ) :=
      ⟨⟨kernelMixedCocycle res d g, continuous_of_discreteTopology⟩,
        kernelMixedCocycle_isCocycle res d ha hN g⟩
    exact galoisRestrictionKernel_hilbert90 K L E z
  obtain ⟨a', _, hl, hr⟩ := exists_mixed_zero_twoCocycle res
    (AlgEquiv.restrictNormalHom_surjective L) d ha hN hm
  refine ⟨a + a', correctTwoCocycle_isCocycle c hc _, ?_, ?_⟩
  · simpa only [d, correctTwoCocycle_add] using hl
  · simpa only [d, correctTwoCocycle_add] using hr

end LocalClassFieldTheory
