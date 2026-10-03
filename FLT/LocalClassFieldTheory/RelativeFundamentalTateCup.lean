/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeTateClasses
public import FLT.LocalClassFieldTheory.TateCupUnit

/-!
# Cup with the relative fundamental class in all Tate degrees

The local fundamental class acts by its constructed two-extension. The map is
on the actual Tate cohomology of the finite Galois group, also in negative
and zero degrees. Its value on the scalar unit is the normalized Tate generator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory groupCohomology

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) [IsGalois K E]
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C
local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(C/K) →* Gal(E/K)))

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [FiniteDimensional K E]

local notation "d" => Module.finrank K E

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

/-- The relative fundamental class in the ordinary finite-group cochain complex. -/
def relativeFundamentalOrdinaryClass :
    groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 :=
  (finiteContinuousCohomologyIso ℤ Gal(E/K) (Additive Eˣ) 2).hom
    (relativeFundamentalClass R S K C E)

/-- Cup with the relative fundamental class, in every integer Tate degree. -/
def relativeFundamentalTateCup (n : ℤ) :
    tateCohomology (Rep.trivial ℤ Gal(E/K) ℤ) n ⟶
      tateCohomology (Rep.ofAlgebraAutOnUnits K E) (n + 2) :=
  tateTwoClassMap _ (relativeFundamentalOrdinaryClass R S K C E) n

/-- The actual cup takes the scalar unit to the previously constructed relative Tate class. -/
theorem relativeFundamentalTateCup_unit :
    relativeFundamentalTateCup R S K C E 0 (tateScalarUnit ℤ Gal(E/K)) =
      relativePositiveTateEquiv K C E 2 (relativeFundamentalClass R S K C E) :=
  tateTwoClassMap_unit_eq _ (relativeFundamentalOrdinaryClass R S K C E)

/-- Any ordinary cocycle representative computes the relative fundamental cup. -/
theorem relativeFundamentalTateCup_representative
    (c : cocycles₂ (Rep.ofAlgebraAutOnUnits K E))
    (hc : H2π _ c = relativeFundamentalOrdinaryClass R S K C E) (n : ℤ) :
    relativeFundamentalTateCup R S K C E n =
      tateTwoExtensionMap (Rep.ofAlgebraAutOnUnits K E) c n := by
  change tateTwoClassMap _ (relativeFundamentalOrdinaryClass R S K C E) n = _
  rw [← hc]
  exact tateTwoClassMap_class _ c n

end LocalClassFieldTheory
