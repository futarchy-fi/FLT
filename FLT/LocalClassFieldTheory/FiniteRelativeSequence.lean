/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteInflationRestrictionExact
public import FLT.LocalClassFieldTheory.FiniteContinuousComparison
public import FLT.LocalClassFieldTheory.ExactSequenceCardBound

/-!
# The relative H² sequence over an intermediate field

Identify the restriction kernel with the Galois group over the intermediate
field. The proved inflation-restriction exactness then gives an exact sequence
whose three terms are the actual relative field-unit cohomology groups.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L]
  (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)))

/-- Ordinary cohomology of the restriction kernel is cohomology over the intermediate field. -/
def relativeKernelCohomologyIso (n : ℕ) :
    groupCohomology (Rep.of (Representation.ofDistribMulAction ℤ N (Additive Lˣ))) n ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits E L) n :=
  groupCohomology.mapIso (galoisRestrictionKernelEquiv K L E)
    (LinearEquiv.refl ℤ (Additive Lˣ)) (fun _ => rfl) n

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]
  [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

/-- Continuous kernel cohomology identifies with ordinary relative cohomology. -/
def finiteRelativeKernelIso (n : ℕ) :
    continuousCohomology ℤ N (Additive Lˣ) n ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits E L) n :=
  finiteContinuousCohomologyIso ℤ N (Additive Lˣ) n ≪≫ relativeKernelCohomologyIso K L E n

/-- The actual restriction map with its kernel group identified. -/
def finiteRelativeRestriction : continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2 ⟶
    groupCohomology (Rep.ofAlgebraAutOnUnits E L) 2 :=
  galoisKernelRestriction K L E 2 ≫ (finiteRelativeKernelIso K L E 2).hom

/-- Inflation followed by the identified restriction is zero. -/
theorem finiteRelative_comp_zero :
    galoisMultiplicativeInflation K L E 2 ≫ finiteRelativeRestriction K L E = 0 := by
  ext x
  change (finiteRelativeKernelIso K L E 2).hom.hom
    ((galoisKernelRestriction K L E 2).hom
      ((galoisMultiplicativeInflation K L E 2).hom x)) = 0
  rw [finiteInflationRestriction_zero, map_zero]

/-- The relative three-term sequence uses the genuine arithmetic maps. -/
def finiteRelativeSequence : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (galoisMultiplicativeInflation K L E 2) (finiteRelativeRestriction K L E)
    (finiteRelative_comp_zero K L E)

/-- Exactness is inherited from the proved finite inflation-restriction theorem. -/
theorem finiteRelativeSequence_exact : (finiteRelativeSequence K L E).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  apply (finiteInflationRestrictionExact K L E x).mp
  have hi := (ModuleCat.mono_iff_injective (finiteRelativeKernelIso K L E 2).hom).1
    inferInstance
  apply hi
  change (finiteRelativeKernelIso K L E 2).hom.hom
    ((galoisKernelRestriction K L E 2).hom x) = 0 at hx
  simpa only [map_zero] using hx

end LocalClassFieldTheory
