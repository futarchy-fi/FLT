/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousInflationCocycleDescent
public import FLT.LocalClassFieldTheory.FiniteInflationRestrictionExact

/-!
# Continuous multiplicative inflation-restriction exactness

For any Galois tower, the image of H2 inflation is exactly the kernel of
restriction. Compatible finite-stage descent and finite Hilbert 90 supply
the correction, and the actual cohomology comparison identifies its class.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "res" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]
  [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

/-- Zero kernel restriction has an actual continuous H2 inflation preimage. -/
theorem continuousInflationRestriction_preimage
    (x : continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2)
    (hx : (galoisKernelRestriction K L E 2).hom x = 0) :
    ∃ y, (galoisMultiplicativeInflation K L E 2).hom y = x := by
  obtain ⟨c, hc, rfl⟩ := integralH2Class_surjective x
  obtain ⟨b, hb⟩ := (galoisKernelRestriction_class_eq_zero K L E c hc).mp hx
  obtain ⟨d, hd, a, ha⟩ := continuousInflationCocycleDescent K L E c hc b
    (fun n m => (hb n m).symm)
  refine ⟨integralH2Class (k := ℤ) d hd, ?_⟩
  change (HomologicalComplex.homologyMap (continuousRestriction res
    (InfiniteGalois.restrictNormalHom_continuous E) (galoisInflationCoefficients K L E)) 2).hom
      (integralH2Class (k := ℤ) d hd) = _
  rw [continuousInflationH2_class]
  apply Eq.symm
  apply (integralH2Class_eq_iff _ _ _ _).mpr
  refine ⟨a, fun g h => ?_⟩
  change g • a h - a (g * h) + a g =
    c (g, h) - (galoisInflationCoefficients K L E).hom (d (res g, res h))
  rw [ha]
  dsimp only [correctTwoCocycle]
  abel

/-- Exactness of the actual continuous multiplicative H2 maps for an arbitrary Galois tower. -/
theorem continuousInflationRestrictionExact :
    Function.Exact (galoisMultiplicativeInflation K L E 2).hom
      (galoisKernelRestriction K L E 2).hom := by
  intro x
  constructor
  · exact continuousInflationRestriction_preimage K L E x
  · rintro ⟨y, rfl⟩
    exact finiteInflationRestriction_zero K L E y

/-- The continuous descended class is independent of the finite stage and all correction choices. -/
theorem continuousInflationRestriction_unique
    (x : continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2)
    (hx : (galoisKernelRestriction K L E 2).hom x = 0) :
    ∃! y, (galoisMultiplicativeInflation K L E 2).hom y = x := by
  obtain ⟨y, hy⟩ := continuousInflationRestriction_preimage K L E x hx
  exact ⟨y, hy, fun z hz => galoisMultiplicativeInflationH2_injective K L E (hz.trans hy.symm)⟩

end LocalClassFieldTheory
