/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteInflationCocycleDescent
public import FLT.LocalClassFieldTheory.GaloisKernelRestriction
public import FLT.LocalClassFieldTheory.IntegralTwoClassEquality

/-!
# Finite inflation-restriction exactness in degree two

The image of multiplicative inflation equals the kernel of restriction
for a finite Galois tower. The preimage class is unique, so the section
and the Hilbert 90 witnesses used to construct it do not affect the result.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [FiniteDimensional K L] (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "res" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]
  [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

/-- Every class with zero restriction is inflated from the intermediate field. -/
theorem finiteInflationRestriction_preimage (x : continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2)
    (hx : (galoisKernelRestriction K L E 2).hom x = 0) :
    ∃ y, (galoisMultiplicativeInflation K L E 2).hom y = x := by
  obtain ⟨c, hc, rfl⟩ := integralH2Class_surjective x
  obtain ⟨b, hb⟩ := (galoisKernelRestriction_class_eq_zero K L E c hc).mp hx
  obtain ⟨d, hd, a, ha⟩ := finiteInflationCocycleDescent K L E c hc b
    (fun n m => (hb n m).symm)
  let dc : C(Gal(E/K) × Gal(E/K), Additive Eˣ) := ⟨d, continuous_of_discreteTopology⟩
  refine ⟨integralH2Class (k := ℤ) dc hd, ?_⟩
  change (HomologicalComplex.homologyMap (continuousRestriction res
    (InfiniteGalois.restrictNormalHom_continuous E) (galoisInflationCoefficients K L E)) 2).hom
      (integralH2Class (k := ℤ) dc hd) = _
  rw [continuousInflationH2_class]
  apply Eq.symm
  apply (integralH2Class_eq_iff _ _ _ _).mpr
  refine ⟨⟨a, continuous_of_discreteTopology⟩, fun g h => ?_⟩
  change g • a h - a (g * h) + a g =
    c (g, h) - (galoisInflationCoefficients K L E).hom (d (res g, res h))
  rw [ha]
  dsimp only [correctTwoCocycle]
  abel

omit [FiniteDimensional K L] in
/-- Restriction annihilates every inflated class. -/
theorem finiteInflationRestriction_zero (y : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2) :
    (galoisKernelRestriction K L E 2).hom
      ((galoisMultiplicativeInflation K L E 2).hom y) = 0 := by
  obtain ⟨c, hc, rfl⟩ := integralH2Class_surjective y
  change (galoisKernelRestriction K L E 2).hom
    ((HomologicalComplex.homologyMap (continuousRestriction res
      (InfiniteGalois.restrictNormalHom_continuous E) (galoisInflationCoefficients K L E)) 2).hom
        (integralH2Class (k := ℤ) c hc)) = 0
  rw [continuousInflationH2_class, galoisKernelRestriction_class_eq_zero]
  refine ⟨ContinuousMap.const _ ((galoisInflationCoefficients K L E).hom (c (1, 1))), ?_⟩
  intro g h
  change (g : Gal(L/K)) • (galoisInflationCoefficients K L E).hom (c (1, 1)) -
      (galoisInflationCoefficients K L E).hom (c (1, 1)) +
      (galoisInflationCoefficients K L E).hom (c (1, 1)) =
    (galoisInflationCoefficients K L E).hom (c (res g, res h))
  rw [show res g = 1 from g.property, show res h = 1 from h.property, sub_add_cancel]
  have he : (galoisInflationCoefficients K L E).hom (res g • c (1, 1)) =
      (g : Gal(L/K)) • (galoisInflationCoefficients K L E).hom (c (1, 1)) :=
    Rep.hom_comm_apply (galoisInflationCoefficients K L E) g _
  rw [show res g = 1 from g.property, one_smul] at he
  exact he.symm

/-- Image equals kernel for the actual finite multiplicative H2 maps. -/
theorem finiteInflationRestrictionExact :
    Function.Exact (galoisMultiplicativeInflation K L E 2).hom
      (galoisKernelRestriction K L E 2).hom := by
  intro x
  constructor
  · exact finiteInflationRestriction_preimage K L E x
  · rintro ⟨y, rfl⟩
    exact finiteInflationRestriction_zero K L E y

/-- The descended class is independent of all section and correction choices. -/
theorem finiteInflationRestriction_unique (x : continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2)
    (hx : (galoisKernelRestriction K L E 2).hom x = 0) :
    ∃! y, (galoisMultiplicativeInflation K L E 2).hom y = x := by
  obtain ⟨y, hy⟩ := finiteInflationRestriction_preimage K L E x hx
  exact ⟨y, hy, fun z hz => galoisMultiplicativeInflationH2_injective K L E (hz.trans hy.symm)⟩

end LocalClassFieldTheory
