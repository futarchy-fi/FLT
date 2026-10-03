/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralUnitInvariants

/-!
# Cohomology of the invariant integral units

The coefficient and group identifications induce an isomorphism on the
actual inhomogeneous cohomology, in every degree.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory
set_option backward.isDefEq.respectTransparency false

variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsGalois K L] (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] integralUnitAction

local notation "ρ" => Representation.ofDistribMulAction ℤ Gal(L/K) (IntegralUnitModule R L)

/-- Cohomology of invariant units is cohomology of the canonical finite-stage units. -/
def integralUnitInvariantCohomologyIso (i : ℕ) :
    groupCohomology (Rep.of ((ρ).quotientToInvariants E.fixingSubgroup)) i ≅
      groupCohomology (integralUnitRep R (integralClosure R E) K E) i := by
  apply CategoryTheory.Iso.symm
  refine groupCohomology.mapIso (integralUnitQuotientEquiv K L E).symm
    (integralUnitInvariantEquiv R K L E) ?_ i
  intro g
  apply LinearMap.ext
  intro u
  change integralUnitInvariantEquiv R K L E (g • (show IntegralUnitModule R E from u)) = _
  have h := integralUnitInvariantEquiv_equivariant R K L E
    ((integralUnitQuotientEquiv K L E).symm g) u
  convert h using 1
  simp only [MulEquiv.apply_symm_apply]

end LocalClassFieldTheory
