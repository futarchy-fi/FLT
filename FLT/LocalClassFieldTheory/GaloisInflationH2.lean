/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousInflationH2
public import FLT.LocalClassFieldTheory.GaloisInflationCoefficients

/-!
# Injective multiplicative inflation in a Galois tower

Continuous Hilbert 90 and fixed-field descent discharge all hypotheses of
the cochain descent theorem for the actual multiplicative inflation map.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]
  [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

local notation "res" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))

/-- Multiplicative inflation for an arbitrary intermediate Galois field. -/
def galoisMultiplicativeInflation (n : ℕ) :
    continuousCohomology ℤ Gal(E/K) (Additive Eˣ) n ⟶
      continuousCohomology ℤ Gal(L/K) (Additive Lˣ) n :=
  homologyMap (continuousRestriction res (InfiniteGalois.restrictNormalHom_continuous E)
    (galoisInflationCoefficients K L E)) n

/-- Multiplicative inflation is injective on continuous H2, with no H2 assumption. -/
theorem galoisMultiplicativeInflationH2_injective :
    Function.Injective (galoisMultiplicativeInflation K L E 2).hom := by
  apply continuousInflationH2_injective
  · exact (InfiniteGalois.restrictNormalHom_continuous E).isClosedMap.isQuotientMap
      (InfiniteGalois.restrictNormalHom_continuous E) (AlgEquiv.restrictNormalHom_surjective L)
  · exact galoisInflationCoefficients_injective K L E
  · exact galoisInflationCoefficients_fixed K L E
  · exact galoisRestrictionKernel_hilbert90 K L E

end LocalClassFieldTheory
