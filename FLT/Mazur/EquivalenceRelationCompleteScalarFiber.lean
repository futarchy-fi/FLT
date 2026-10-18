/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteClosedLocus
public import FLT.Mazur.SchemeFiniteGroupFiniteFiberTests

/-!
# Exact scalar-fiber completeness of the original normalized source

The closed complete locus descends to the actual finite-group quotient of any
stable affine chart. Its defining ideal gives an exact power-equation test for
completeness of every point over an original scalar prime. The equations are
characterized here; they are not asserted for arbitrary original scalar maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source invariantScalarCoordinates action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "C" => U.ι ⁻¹' completePointLocus (p := p) (q := q) I o

/-- The unchanged complete points in an affine chart form a stable closed subset. -/
theorem completeChart_isClosed : IsClosed C :=
  (completePointLocus_isClosed I o).preimage U.ι.continuous

/-- Stability holds for the actual restricted moving action. -/
theorem completeChart_stable (g : Equiv.Perm I) (x : U.toScheme) (hx : x ∈ C) :
    (ρ g).hom x ∈ C := by
  change U.ι ((ρ g).hom x) ∈ completePointLocus I o
  have he := congrArg (fun f : U.toScheme ⟶ source p q I o ↦ f x)
    (restrictedAction_hom_ι (action e I o) U hU g)
  change U.ι ((ρ g).hom x) = (action e I o g).hom (U.ι x) at he
  rw [he]
  change U.ι x ∈ (action e I o g).hom ⁻¹' completePointLocus I o
  rw [completePointLocus_action_invariant]
  exact hx

variable [IsAffine U.toScheme]

/-- The constructed complete orbit image, including points outside the complete interior. -/
def completeAffineOrbitImage : TopologicalSpace.Closeds (quotient ρ) :=
  closedOrbitImage ρ C (completeChart_isClosed I o U)

/-- The ideal is constructed from the unchanged complete locus, before any scalar-prime test. -/
def completeAffineOrbitIdeal : Ideal (invariantCoordinates ρ) :=
  closedOrbitIdeal ρ C (completeChart_isClosed I o U)

/-- Pulling back the closed orbit image gives exactly all original complete chart points. -/
theorem completeAffineOrbitImage_preimage :
    quotientMap ρ ⁻¹' (completeAffineOrbitImage e I o U hU : Set (quotient ρ)) = C :=
  closedOrbitImage_preimage ρ C (completeChart_isClosed I o U)
    (completeChart_stable e I o U hU)

/-- The constructed ideal has exactly the actual complete orbit image as its zero set. -/
theorem completeAffineOrbitIdeal_zeroLocus :
    PrimeSpectrum.zeroLocus (completeAffineOrbitIdeal e I o U hU : Set _) =
      (completeAffineOrbitImage e I o U hU : Set (quotient ρ)) :=
  closedOrbitIdeal_zeroLocus ρ C (completeChart_isClosed I o U)

variable [NoetherianSpace U.toScheme]

/-- A finite family of invariant support functions fixed before any original scalar prime. -/
def completeAffineOrbitTests : Finset (invariantCoordinates ρ) :=
  closedOrbitTests ρ C (completeChart_isClosed I o U)

/-- The finite equations cut out exactly the full original complete orbit image. -/
theorem completeAffineOrbitTests_zeroLocus :
    PrimeSpectrum.zeroLocus (completeAffineOrbitTests e I o U hU : Set _) =
      (completeAffineOrbitImage e I o U hU : Set (quotient ρ)) :=
  closedOrbitTests_zeroLocus ρ C (completeChart_isClosed I o U)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
