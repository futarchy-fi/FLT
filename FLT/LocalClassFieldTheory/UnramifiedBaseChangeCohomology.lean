/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeRestriction
public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeOrder
public import FLT.LocalClassFieldTheory.ContinuousRestriction

/-!
# Multiplicative cohomology maps for unramified base change

The proved field inclusion and continuous Galois restriction define the
actual coefficient and cohomology maps used in change of base.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex

variable (R S K L C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [Field C] [Algebra L C] [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K L C] [IsScalarTower R K C] [IsScalarTower R L C]
  [IsScalarTower S L C] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [Algebra.IsSeparable L C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S L C

attribute [local instance] fieldUnitAction

/-- Field-unit inclusion, equivariant for the actual base-change restriction. -/
def unramifiedBaseChangeCoefficients :
    Rep.res (unramifiedBaseChangeRestriction R S K L C)
      (Rep.of (Representation.ofDistribMulAction ℤ Gal(A/K) (Additive Aˣ))) ⟶
        Rep.of (Representation.ofDistribMulAction ℤ Gal(B/L) (Additive Bˣ)) :=
  Rep.ofHom ⟨(Units.map
    (maximalUnramifiedBaseChange R S K L C).toMonoidHom).toAdditive.toIntLinearMap,
    fun g => by
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Units.ext
      exact unramifiedBaseChangeRestriction_apply R S K L C g ((Additive.toMul x : Aˣ) : A)⟩

variable [TopologicalSpace (Additive (maximalUnramified R K C)ˣ)]
  [DiscreteTopology (Additive (maximalUnramified R K C)ˣ)]
  [TopologicalSpace (Additive (maximalUnramified S L C)ˣ)]
  [DiscreteTopology (Additive (maximalUnramified S L C)ˣ)]

local instance baseChangeSourceGalois : IsGalois K A := maximalUnramified_isGalois R K C
local instance baseChangeTargetGalois : IsGalois L B := maximalUnramified_isGalois S L C

/-- The induced map on actual continuous multiplicative cohomology in every degree. -/
def unramifiedBaseChangeCohomology (n : ℕ) :
    continuousCohomology ℤ Gal(A/K) (Additive Aˣ) n ⟶
      continuousCohomology ℤ Gal(B/L) (Additive Bˣ) n :=
  homologyMap (continuousRestriction (unramifiedBaseChangeRestriction R S K L C)
    (unramifiedBaseChangeRestriction_continuous R S K L C)
    (unramifiedBaseChangeCoefficients R S K L C)) n

omit [TopologicalSpace (Additive (maximalUnramified R K C)ˣ)]
  [DiscreteTopology (Additive (maximalUnramified R K C)ˣ)]
  [TopologicalSpace (Additive (maximalUnramified S L C)ˣ)]
  [DiscreteTopology (Additive (maximalUnramified S L C)ˣ)] in
/-- The actual coefficient map scales additive order by the ramification index. -/
theorem unramifiedBaseChangeCoefficients_order (x : Additive Aˣ) :
    unramifiedUnionOrderAdd S L C ((unramifiedBaseChangeCoefficients R S K L C).hom x) =
      (maximalIdeal R).ramificationIdx' (maximalIdeal S) • unramifiedUnionOrderAdd R K C x := by
  exact congrArg Multiplicative.toAdd (unramifiedUnionOrder_baseChange R S K L C x.toMul)

end LocalClassFieldTheory
