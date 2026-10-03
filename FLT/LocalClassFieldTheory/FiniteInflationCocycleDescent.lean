/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteKernelCocycleCorrection
public import FLT.LocalClassFieldTheory.GaloisInflationCoefficients
public import FLT.LocalClassFieldTheory.KernelCocycleDescent

/-!
# Finite Galois descent of two-cocycles

A two-cocycle with a bounding cochain on the restriction kernel differs
from an inflated cocycle by an explicitly constructed global boundary.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [FiniteDimensional K L] (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "res" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

/-- The finite image-kernel construction on actual field-unit cocycles. -/
theorem finiteInflationCocycleDescent (c : Gal(L/K) × Gal(L/K) → Additive Lˣ)
    (hc : IsCocycle₂ c) (b : (res).ker → Additive Lˣ)
    (hb : ∀ n m : (res).ker, c (n, m) = n • b m - b (n * m) + b n) :
    ∃ (d : Gal(E/K) × Gal(E/K) → Additive Eˣ), IsCocycle₂ d ∧
      ∃ a : Gal(L/K) → Additive Lˣ, ∀ g h,
        (galoisInflationCoefficients K L E).hom (d (res g, res h)) =
          correctTwoCocycle c a (g, h) := by
  obtain ⟨a, ha, hl, hr⟩ := finiteKernelCocycleCorrection K L E c hc b hb
  obtain ⟨d, hd, he⟩ := exists_descended_twoCocycle res (correctTwoCocycle c a) ha hl hr
    (AlgEquiv.restrictNormalHom_surjective L)
    (galoisInflationCoefficients K L E).hom.toLinearMap.toAddMonoidHom
    (galoisInflationCoefficients_injective K L E)
    (fun g u => Rep.hom_comm_apply (galoisInflationCoefficients K L E) g u)
    (fun m hm => galoisInflationCoefficients_fixed K L E m (fun n hn => hm ⟨n, hn⟩))
  exact ⟨d, hd, a, he⟩

end LocalClassFieldTheory
