/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.PeuRamifiedClass
public import FLT.GaloisRepresentation.Extensions.LinearCoefficientMap

/-!
# Linear transport of the independent cup annihilator

Equivariant coefficient maps transport actual continuous bounding cochains.
The resulting annihilator is a submodule of continuous cocycles.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open GaloisRepresentation.Extensions

variable {G F M N : Type*} [Group G] [TopologicalSpace G]
  [Field F] [TopologicalSpace F] [DiscreteTopology F]
  [AddCommGroup M] [Module F M] [DistribMulAction G M] [SMulCommClass G F M]
  [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup N] [Module F N] [DistribMulAction G N] [SMulCommClass G F N]
  [TopologicalSpace N] [DiscreteTopology N]

omit [TopologicalSpace F] [DiscreteTopology F] [SMulCommClass G F M]
  [SMulCommClass G F N] [DiscreteTopology N] in
/-- An equivariant linear map transports a continuous bounding cochain. -/
theorem continuousBoundary_map (f : M →ₗ[F] N)
    (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (z : C(G × G, M)) (hz : ContinuousIsCoboundaryTwo z) :
    ContinuousIsCoboundaryTwo
      (⟨fun gh => f (z gh), (continuous_of_discreteTopology (f := f)).comp
        z.continuous⟩ : C(G × G, N)) := by
  obtain ⟨t, ht⟩ := hz
  refine ⟨⟨fun g => f (t g), (continuous_of_discreteTopology (f := f)).comp
    t.continuous⟩, fun g h => ?_⟩
  simpa only [ContinuousMap.coe_mk, map_add, map_sub, hf] using congrArg f (ht g h)

/-- Continuous boundaries are closed under addition. -/
theorem continuousBoundary_add (z w : C(G × G, M))
    (hz : ContinuousIsCoboundaryTwo z) (hw : ContinuousIsCoboundaryTwo w) :
    ContinuousIsCoboundaryTwo (z + w) := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨u, hu⟩ := hw
  refine ⟨t + u, fun g h => ?_⟩
  change g • (t h + u h) - (t (g * h) + u (g * h)) + (t g + u g) = _
  rw [smul_add]
  have he := congrArg₂ (· + ·) (ht g h) (hu g h)
  dsimp only [ContinuousMap.add_apply]
  calc
    _ = (g • t h - t (g * h) + t g) + (g • u h - u (g * h) + u g) := by abel
    _ = _ := he

omit [TopologicalSpace F] [DiscreteTopology F] in
/-- Continuous boundaries are closed under scalar multiplication. -/
theorem continuousBoundary_smul (a : F) (z : C(G × G, M))
    (hz : ContinuousIsCoboundaryTwo z) : ContinuousIsCoboundaryTwo (a • z) := by
  obtain ⟨t, ht⟩ := hz
  refine ⟨a • t, fun g h => ?_⟩
  change g • (a • t h) - a • t (g * h) + a • t g = a • z (g, h)
  rw [smul_comm g, ← smul_sub, ← smul_add, ht]

/-- Continuous boundaries are closed under finite sums. -/
theorem continuousBoundary_sum {ι : Type*} (s : Finset ι) (z : ι → C(G × G, M))
    (hz : ∀ i ∈ s, ContinuousIsCoboundaryTwo (z i)) :
    ContinuousIsCoboundaryTwo (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact continuousBoundary_add _ _ (hz i (by simp)) (ih (fun j hj => hz j (by simp [hj])))

/-- The independent annihilator forms a submodule already on actual continuous cocycles. -/
def peuCocycleSubmodule (I : Subgroup G) : Submodule F (linearContinuousCocycles F G M) where
  carrier := {c | IsPeuRamifiedCocycle (k := F) I ⟨c.1, c.2⟩}
  zero_mem' := by
    intro d _
    exact ⟨0, by simp [continuousCup]⟩
  add_mem' := by
    intro c e hc he d hd
    convert continuousBoundary_add (continuousCup ⟨c.1, c.2⟩ d)
      (continuousCup ⟨e.1, e.2⟩ d) (hc d hd) (he d hd) using 1
    apply ContinuousMap.ext
    intro gh
    exact smul_add _ _ _
  smul_mem' := by
    intro a c hc d hd
    have h := continuousBoundary_smul a (continuousCup ⟨c.1, c.2⟩ d) (hc d hd)
    convert h using 1
    apply ContinuousMap.ext
    intro gh
    exact smul_comm _ _ _

/-- A linear equivariant coefficient isomorphism preserves and reflects the predicate. -/
theorem isPeuRamified_linearEquiv_iff (I : Subgroup G) (e : M ≃ₗ[F] N)
    (he : ∀ (g : G) (x : M), e (g • x) = g • e x)
    (c : linearContinuousCocycles F G M) :
    linearCocycleMap e.toLinearMap he c ∈ peuCocycleSubmodule (M := N) I ↔
      c ∈ peuCocycleSubmodule (M := M) I := by
  have hs (g : G) (x : N) : e.symm (g • x) = g • e.symm x := by
    apply e.injective
    simp only [e.apply_symm_apply, he]
  constructor
  · intro hc d hd
    have h := continuousBoundary_map e.symm.toLinearMap hs _ (hc d hd)
    convert h using 1
    apply ContinuousMap.ext
    intro gh
    change _ = e.symm (d.1 gh.2 • e (c.1 gh.1))
    rw [map_smul, e.symm_apply_apply]
    rfl
  · intro hc d hd
    convert continuousBoundary_map e.toLinearMap he _ (hc d hd) using 1
    apply ContinuousMap.ext
    intro gh
    exact (map_smul e _ _).symm

end LocalClassFieldTheory
