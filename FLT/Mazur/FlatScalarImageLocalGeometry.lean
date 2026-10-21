/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarImagePrincipalFactor
public import FLT.Mazur.FlatScalarImageProjection
public import FLT.Mazur.ScalarImageNeighborhoodBasis
public import FLT.Mazur.SchemePullbackThroughOpen

/-!
# Canonical branches factor through every original image neighborhood

A neighborhood of the image point above an original prime contains the
entire image of that prime's canonical branch. Geometry stable under base
change transfers from the original neighborhood to the full branch.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FlatScalarImageBaseChange
open FlatScalarSchemeBaseChange SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (X : Scheme.{0}) [Algebra R Γ(X, ⊤)]
  [CompactSpace X] [QuasiSeparatedSpace X] (x : PrimeSpectrum R)
set_option quotPrecheck false
local notation "L" => ScalarPrimeLocalizationCover.Branch x
local notation "b₀" =>
  SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤))
local notation "b₁" => base R L X
variable (y : Spec (.of (Scalars
    (SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤))))))
  (hyx : inclusion (SchemeScalarPrincipalNeighborhood.scalarMorphism
    (algebraMap R Γ(X, ⊤))) y = x)
  (U : (Spec (.of (Scalars
    (SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤)))))).Opens)
  (hy : y ∈ U)

include hyx hy in
/-- Every point of the canonical branch image lies in the original image neighborhood. -/
theorem canonicalImage_range_subset : Set.range (imageMap R L X) ⊆ (U : Set _) := by
  obtain ⟨r, hr, hU⟩ := exists_original_principal_over b₀ x y hyx U hy
  exact (imageMap_range_subset_principal R L X r (canonicalBranch_isUnit R x r hr)).trans hU

/-- The entire canonical branch image factors through an arbitrary original neighborhood. -/
def localImageMap : Spec (.of (Scalars b₁)) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (imageMap R L X)
    (by simpa using canonicalImage_range_subset R X x y hyx U hy)

/-- The local factorization retains the exact original image map. -/
@[reassoc] theorem localImageMap_ι :
    localImageMap R X x y hyx U hy ≫ U.ι = imageMap R L X :=
  IsOpenImmersion.lift_fac _ _ _

include hyx hy in
/-- Geometry on any original image neighborhood transfers to the whole canonical branch. -/
theorem projection_property_of_neighborhood (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] (hP : P ((projection b₀) ∣_ U)) : P (projection b₁) :=
  SchemePullbackThroughOpen.property (projection_isPullback R L X) U
    (localImageMap R X x y hyx U hy) (localImageMap_ι R X x y hyx U hy) P hP

end FLT.Mazur.FlatScalarImageBaseChange
