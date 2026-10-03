/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteKernelCocycleCorrection

/-!
# Finite correction for a normal Galois subgroup

The Galois correspondence identifies a normal subgroup with the restriction
kernel of its fixed field, allowing finite kernel correction to apply.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [FiniteDimensional K L] (N : Subgroup Gal(L/K)) [N.Normal]

attribute [local instance] fieldUnitAction

/-- A finite normal subgroup has mixed-term correction with no cohomological premise. -/
theorem finiteSubgroupCocycleCorrection (c : Gal(L/K) × Gal(L/K) → Additive Lˣ)
    (hc : IsCocycle₂ c) (b : N → Additive Lˣ)
    (hb : ∀ n m : N, c (n, m) = n • b m - b (n * m) + b n) :
    ∃ a : Gal(L/K) → Additive Lˣ, IsCocycle₂ (correctTwoCocycle c a) ∧
      (∀ n : N, ∀ g, correctTwoCocycle c a (n, g) = 0) ∧
      (∀ g, ∀ n : N, correctTwoCocycle c a (g, n) = 0) := by
  let E := IntermediateField.fixedField N
  let r := (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
  have hker : r.ker = N :=
    E.restrictNormalHom_ker.trans (IntermediateField.fixingSubgroup_fixedField N)
  let e : r.ker →* N :=
    { toFun := fun n => ⟨n, hker ▸ n.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let : TopologicalSpace (Additive Lˣ) := ⊥
  let : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  obtain ⟨a, ha, hl, hr⟩ := finiteKernelCocycleCorrection K L E c hc (fun n => b (e n))
    (fun n m => hb (e n) (e m))
  refine ⟨a, ha, ?_, ?_⟩
  · intro n g
    exact hl ⟨n, hker.symm ▸ n.property⟩ g
  · intro g n
    exact hr g ⟨n, hker.symm ▸ n.property⟩

end LocalClassFieldTheory
