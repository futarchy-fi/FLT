/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeRestrictionTower

/-!
# Inflation in a finite relative Galois tower

Inflate from Gal(E/K) to Gal(F/K) and include E's units in F's units.
Further inflation to the common closure equals direct inflation from E.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (E : IntermediateField K C) (F : IntermediateField E C)
  [IsGalois K E] [IsGalois K (F.restrictScalars K)]
  [FiniteDimensional K (F.restrictScalars K)]

attribute [local instance] fieldUnitAction

/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeInflationGalois : IsGalois K F :=
  inferInstanceAs (IsGalois K (F.restrictScalars K))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeInflationFinite : FiniteDimensional K F :=
  inferInstanceAs (FiniteDimensional K (F.restrictScalars K))

/-- The intermediate base acts on either presentation of the top field. -/
local instance relativeInflationMiddleAlgebra : Algebra E (F.restrictScalars K) :=
  inferInstanceAs (Algebra E F)
/-- The base-field tower is unchanged by forgetting the intermediate-field structure. -/
local instance relativeInflationMiddleTower : IsScalarTower K E (F.restrictScalars K) :=
  inferInstanceAs (IsScalarTower K E F)
/-- The embedding into the common closure is compatible with the intermediate base. -/
local instance relativeInflationClosureTower : IsScalarTower E (F.restrictScalars K) C :=
  inferInstanceAs (IsScalarTower E F C)

/-- Inclusion of units with the action pulled back along relative Galois restriction. -/
def relativeInflationCoefficients :
    Rep.res (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
      (Rep.of (Representation.ofDistribMulAction ℤ Gal(E/K) (Additive Eˣ))) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ Gal(F/K) (Additive Fˣ)) :=
  Rep.ofHom ⟨(Units.map (algebraMap E F).toMonoidHom).toAdditive.toIntLinearMap,
    fun g => by
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Units.ext
      exact g.restrictNormal_commutes E (Additive.toMul u : Eˣ)⟩

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]

/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeInflationUnitTopology : TopologicalSpace (Additive (F.restrictScalars K)ˣ) :=
  inferInstanceAs (TopologicalSpace (Additive Fˣ))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeInflationUnitDiscrete : DiscreteTopology (Additive (F.restrictScalars K)ˣ) :=
  inferInstanceAs (DiscreteTopology (Additive Fˣ))

/-- Actual finite relative inflation on continuous cochains. -/
def relativeInflationComplex : continuousCochains ℤ Gal(E/K) (Additive Eˣ) ⟶
    continuousCochains ℤ Gal(F/K) (Additive Fˣ) :=
  continuousRestriction (AlgEquiv.restrictNormalHom E)
    continuous_of_discreteTopology (relativeInflationCoefficients K C E F)

/-- Actual finite relative inflation on cohomology. -/
def relativeInflation (n : ℕ) : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) n ⟶
    continuousCohomology ℤ Gal(F/K) (Additive Fˣ) n :=
  homologyMap (relativeInflationComplex K C E F) n

omit [IsGalois K C] [FiniteDimensional K (F.restrictScalars K)]
  [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)] in
/-- Successive restriction of automorphisms agrees with direct restriction. -/
theorem relativeInflation_group_tower (g : Gal(C/K)) :
    AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom (F.restrictScalars K) g) =
      AlgEquiv.restrictNormalHom E g :=
  (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E (F.restrictScalars K) g).symm

/-- Successive relative inflation agrees with direct inflation on cochains. -/
theorem relativeInflation_tower_complex :
    relativeInflationComplex K C E F ≫
      continuousRestriction (AlgEquiv.restrictNormalHom (F.restrictScalars K))
        (InfiniteGalois.restrictNormalHom_continuous (F.restrictScalars K))
        (galoisInflationCoefficients K C (F.restrictScalars K)) =
      continuousRestriction (AlgEquiv.restrictNormalHom E)
        (InfiniteGalois.restrictNormalHom_continuous E)
        (galoisInflationCoefficients K C E) := by
  ext n c : 3
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Units.ext
  change (algebraMap F C) (algebraMap E F
    (c.val (fun i => AlgEquiv.restrictNormalHom E
      (AlgEquiv.restrictNormalHom (F.restrictScalars K) (g i)))).toMul) = _
  rw [← IsScalarTower.algebraMap_apply]
  simp only [relativeInflation_group_tower]
  rfl

/-- The tower identity holds for the induced maps in every cohomological degree. -/
theorem relativeInflation_tower (n : ℕ) :
    relativeInflation K C E F n ≫
      galoisMultiplicativeInflation K C (F.restrictScalars K) n =
        galoisMultiplicativeInflation K C E n := by
  unfold relativeInflation galoisMultiplicativeInflation
  rw [← homologyMap_comp, relativeInflation_tower_complex]

/-- Inflation in the finite tower is injective on H². -/
theorem relativeInflationH2_injective :
    Function.Injective (relativeInflation K C E F 2).hom := by
  intro x y h
  apply galoisMultiplicativeInflationH2_injective K C E
  have ht := congrArg (fun f => f.hom) (relativeInflation_tower K C E F 2)
  rw [← ht]
  exact congrArg (galoisMultiplicativeInflation K C (F.restrictScalars K) 2).hom h

end LocalClassFieldTheory
