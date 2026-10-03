/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousInflationRestrictionExact
public import FLT.LocalClassFieldTheory.RelativeRestrictionKernel
public import FLT.LocalClassFieldTheory.UnramifiedBaseChangeInflationSquare
public import FLT.LocalClassFieldTheory.UnramifiedInvariantRestriction
public import FLT.LocalClassFieldTheory.UnramifiedInflationInjective

/-!
# Relative preimages of degree-torsion unramified classes

Degree multiplication kills these classes after changing base. The actual
inflation/restriction square and proved exactness then produce relative H2
preimages. No relative order or exactness is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex

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

omit [IsGalois K E] in
/-- A degree-torsion unramified class becomes zero after base change. -/
theorem unramifiedDegreeTorsion_baseChange_zero (x : relativeRestrictionKernel d) :
    (unramifiedBaseChangeCohomology R S K E C 2).hom
      ((unramifiedMultiplicativeInvariant R K C).symm x.val) = 0 := by
  apply (unramifiedMultiplicativeInvariant S E C).injective
  rw [map_zero, unramifiedMultiplicativeInvariant_baseChange, AddEquiv.apply_symm_apply]
  exact x.property

include S

/-- The absolute inflation of every degree-torsion unramified class is killed by
restriction to the actual relative kernel. -/
theorem unramifiedDegreeTorsion_kernel_zero (x : relativeRestrictionKernel d) :
    (galoisKernelRestriction K C E 2).hom
      ((unramifiedMultiplicativeInflation R K C 2).hom
        ((unramifiedMultiplicativeInvariant R K C).symm x.val)) = 0 := by
  have h := congrArg (fun t => t.hom ((unramifiedMultiplicativeInvariant R K C).symm x.val))
    (unramifiedBaseChangeInflation_cohomology R S K C E 2)
  change (unramifiedKernelInflation S K C E 2).hom
      ((unramifiedBaseChangeCohomology R S K E C 2).hom _) = _ at h
  rw [unramifiedDegreeTorsion_baseChange_zero, map_zero] at h
  exact h.symm

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

/-- A relative H2 preimage exists by the already proved continuous exactness theorem. -/
theorem relativeDegreeTorsion_preimage (x : relativeRestrictionKernel d) :
    ∃ y, (galoisMultiplicativeInflation K C E 2).hom y =
      (unramifiedMultiplicativeInflation R K C 2).hom
        ((unramifiedMultiplicativeInvariant R K C).symm x.val) :=
  continuousInflationRestriction_preimage K C E _
    (unramifiedDegreeTorsion_kernel_zero R S K C E x)

/-- The relative H2 class supplied by exactness for an actual degree-torsion invariant. -/
def relativeDegreeTorsionClass (x : relativeRestrictionKernel d) :
    continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 :=
  (relativeDegreeTorsion_preimage R S K C E x).choose

/-- The constructed relative class inflates to the unramified class with the given invariant. -/
theorem relativeDegreeTorsionClass_inflation (x : relativeRestrictionKernel d) :
    (galoisMultiplicativeInflation K C E 2).hom (relativeDegreeTorsionClass R S K C E x) =
      (unramifiedMultiplicativeInflation R K C 2).hom
        ((unramifiedMultiplicativeInvariant R K C).symm x.val) :=
  (relativeDegreeTorsion_preimage R S K C E x).choose_spec

end LocalClassFieldTheory
