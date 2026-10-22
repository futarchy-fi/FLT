/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRigidity
public import FLT.Mazur.SchemeScalarOrbitComparison

/-!
# Original-scalar orbit comparisons on normalized boundary charts

The actual normalized action is free. Its orbit relation is therefore a
constructed closed subscheme of the tensor product over the prescribed
original scalar map. This does not assert that its balancing ideal vanishes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarOrbitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R : Type} [CommRing R]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU

/-- The genuine original-scalar chart orbit comparison is a constructed closed immersion. -/
theorem originalChartOrbit_closedImmersion : IsClosedImmersion (orbitArrow ρ s) :=
  orbitArrow_closedImmersion ρ s (boundaryChart_action_free n o U e hU)

/-- All actual invariant section differences generate its full nonreduced defining ideal. -/
theorem originalChartOrbit_ker :
    let _ := sourceAlgebra ρ s
    RingHom.ker (coordinates ρ s) =
      Ideal.span (Set.range (fun a : invariantCoordinates ρ ↦
        (a.val ⊗ₜ[R] (1 : Γ(U.toScheme, ⊤))) - (1 ⊗ₜ[R] a.val))) :=
  coordinates_ker ρ s (boundaryChart_action_free n o U e hU)

/-- Scalar fullness identifies the actual original chart comparison, with no base replacement. -/
theorem originalChartOrbit_bijective_of_full (hfull : Function.Surjective s) :
    Function.Bijective (coordinates ρ s) :=
  coordinates_bijective_of_full ρ s (boundaryChart_action_free n o U e hU) hfull

end FLT.Mazur.EquivalenceRelationNormalizedFrames
