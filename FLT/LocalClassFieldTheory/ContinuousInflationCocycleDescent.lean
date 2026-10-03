/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCocycleQuotient
public import FLT.LocalClassFieldTheory.ContinuousKernelCocycleCorrection

/-!
# Continuous Galois two-cocycle descent

Finite-stage correction followed by quotient continuity gives the full
continuous image-kernel construction, with no finiteness assumption on
either Galois extension in the original tower.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "res" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]
  [TopologicalSpace (Additive Eˣ)]

/-- A continuous cocycle restricting to a boundary is continuously cohomologous to inflation. -/
theorem continuousInflationCocycleDescent
    (c : C(Gal(L/K) × Gal(L/K), Additive Lˣ)) (hc : IsCocycle₂ c)
    (b : C((res).ker, Additive Lˣ))
    (hb : ∀ n m : (res).ker, c (n, m) = n • b m - b (n * m) + b n) :
    ∃ d : C(Gal(E/K) × Gal(E/K), Additive Eˣ), IsCocycle₂ d ∧
      ∃ a : C(Gal(L/K), Additive Lˣ), ∀ g h,
        (galoisInflationCoefficients K L E).hom (d (res g, res h)) =
          correctTwoCocycle c a (g, h) := by
  obtain ⟨a, hl, hr⟩ := continuousKernelCocycleCorrection K L E c hc b hb
  have hs : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective L
  have hp : Continuous (Prod.map res res) :=
    (InfiniteGalois.restrictNormalHom_continuous E).prodMap
      (InfiniteGalois.restrictNormalHom_continuous E)
  have hps : Function.Surjective (Prod.map res res) := by
    rintro ⟨g, h⟩
    obtain ⟨g, rfl⟩ := hs g
    obtain ⟨h, rfl⟩ := hs h
    exact ⟨(g, h), rfl⟩
  obtain ⟨d, hd, he⟩ := exists_continuous_descended_twoCocycle res hs
    (hp.isClosedMap.isQuotientMap hp hps)
    (galoisInflationCoefficients K L E).hom.toLinearMap.toAddMonoidHom
    (galoisInflationCoefficients_injective K L E)
    (fun g u => Rep.hom_comm_apply (galoisInflationCoefficients K L E) g u)
    (fun m hm => galoisInflationCoefficients_fixed K L E m (fun n hn => hm ⟨n, hn⟩))
    (continuousCorrectTwoCocycle c a) (correctTwoCocycle_isCocycle c hc a) hl hr
  exact ⟨d, hd, a, he⟩

end LocalClassFieldTheory
