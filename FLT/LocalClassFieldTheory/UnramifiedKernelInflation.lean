/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisKernelContinuousEquiv
public import FLT.LocalClassFieldTheory.UnramifiedMultiplicativeInflation

/-!
# Unramified inflation over an intermediate field to its restriction kernel

The kernel is identified with the Galois group over the intermediate field.
Restricting its action to that field's unramified union gives the group map,
and inclusion of units gives the actual continuous cohomology map.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex

variable (S K C : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (E : IntermediateField K C) [IsGalois K E]
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [Finite (ResidueField S)] [IsSepClosed C] [IsAdicComplete (maximalIdeal S) S]

local notation "B" => maximalUnramified S E C
local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(C/K) →* Gal(E/K)))

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureUnitTopology separableClosureUnitDiscrete

/-- Restrict the actual kernel's action to the unramified union over the intermediate field. -/
def unramifiedKernelRestriction : N →* Gal(B/E) :=
  (unramifiedRestriction S E C).comp (galoisRestrictionKernelEquiv K C E).toMonoidHom

/-- This restriction is continuous for the actual subgroup and Krull topologies. -/
theorem unramifiedKernelRestriction_continuous :
    Continuous (unramifiedKernelRestriction S K C E) :=
  (unramifiedRestriction_continuous S E C).comp (galoisRestrictionKernelEquiv_continuous K C E)

/-- The restricted action agrees with the original overfield action. -/
theorem unramifiedKernelRestriction_apply (g : N) (x : B) :
    (unramifiedKernelRestriction S K C E g x : C) = g.val (x : C) :=
  AlgEquiv.restrictNormal_apply B (galoisRestrictionKernelEquiv K C E g) x

/-- Inclusion of units is equivariant for the actual kernel action. -/
def unramifiedKernelInflationCoefficients :
    Rep.res (unramifiedKernelRestriction S K C E)
      (Rep.of (Representation.ofDistribMulAction ℤ Gal(B/E) (Additive Bˣ))) ⟶
        Rep.of (Representation.ofDistribMulAction ℤ N (Additive Cˣ)) :=
  Rep.ofHom ⟨(Units.map (B).val.toMonoidHom).toAdditive.toIntLinearMap, fun g => by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    exact unramifiedKernelRestriction_apply S K C E g
      ((Additive.toMul x : (maximalUnramified S E C)ˣ) : maximalUnramified S E C)⟩

/-- Inflation to the restriction kernel on actual continuous cohomology. -/
def unramifiedKernelInflation (n : ℕ) :
    continuousCohomology ℤ Gal(B/E) (Additive Bˣ) n ⟶
      continuousCohomology ℤ N (Additive Cˣ) n :=
  homologyMap (continuousRestriction (unramifiedKernelRestriction S K C E)
    (unramifiedKernelRestriction_continuous S K C E)
    (unramifiedKernelInflationCoefficients S K C E)) n

end LocalClassFieldTheory
