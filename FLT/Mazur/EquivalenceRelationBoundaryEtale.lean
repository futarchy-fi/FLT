/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRigidity
public import FLT.Mazur.SchemeFiniteGroupFreeEtale

/-!
# Etale normalized boundary covers at every original test order

The free normalized action constructs etaleness of the actual chart covers.
They retain the existing finite, surjective and effective-descent structures,
without any Noetherian hypothesis on the original scalar ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open AffineScalarBoundaryNilpotence FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU

/-- The full original boundary product has its constructed finite surjective etale chart. -/
instance chartBoundaryProduct_etale : Etale (chartBoundaryProduct n o U e hU s κ) := by
  let _ := quotientMap_etale_of_free ρ (boundaryChart_action_free n o U e hU)
  unfold chartBoundaryProduct
  infer_instance

variable [Etale p] [TopologicalSpace.NoetherianSpace U.toScheme] (k : ℕ)

/-- Every nonreduced ideal-power test has the same actual etale chart at the same order. -/
instance boundaryTestChartProjection_etale :
    Etale (boundaryTestChartProjection n o U e hU s κ k) := by
  let _ := quotientMap_etale_of_free ρ (boundaryChart_action_free n o U e hU)
  unfold boundaryTestChartProjection
  infer_instance

end FLT.Mazur.EquivalenceRelationNormalizedFrames
