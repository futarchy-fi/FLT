/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarImageBaseChange
public import FLT.Mazur.ScalarPrimeLocalizationCover

/-!
# Principal neighborhoods of the exact original scalar image

A scalar inverted on a flat branch is also invertible in its exact image
quotient. Consequently the whole branch image factors through the original
principal image neighborhood. No reduced image or residue field is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FlatScalarImageBaseChange
open FlatScalarSchemeBaseChange SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (X : Scheme.{0}) [Algebra R Γ(X, ⊤)] [CompactSpace X] [QuasiSeparatedSpace X]
set_option quotPrecheck false
local notation "b₀" =>
  SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤))
local notation "b₁" => base R S X

/-- The neighborhood uses the image of the literal original scalar. -/
def principalImageOpen (r : R) : (Spec (.of (Scalars b₀))).Opens :=
  PrimeSpectrum.basicOpen (quotient b₀ r)

/-- Inverting an original scalar also inverts it in the exact full-image quotient. -/
theorem coefficients_isUnit (r : R) (hr : IsUnit (algebraMap R S r)) :
    IsUnit (coefficients R S X (quotient b₀ r)) :=
  hr.map (quotient b₁)

/-- Every point of the whole branch image lies in the original principal neighborhood. -/
theorem imageMap_range_subset_principal (r : R) (hr : IsUnit (algebraMap R S r)) :
    Set.range (imageMap R S X) ⊆ (principalImageOpen R X r : Set _) := by
  rintro _ ⟨y, rfl⟩ hy
  exact y.isPrime.ne_top
    (y.asIdeal.eq_top_of_isUnit_mem hy (coefficients_isUnit R S X r hr))

/-- The actual image map factored through its original principal neighborhood. -/
def principalImageMap (r : R) (hr : IsUnit (algebraMap R S r)) :
    Spec (.of (Scalars b₁)) ⟶ (principalImageOpen R X r).toScheme :=
  IsOpenImmersion.lift (principalImageOpen R X r).ι (imageMap R S X)
    (by simpa using imageMap_range_subset_principal R S X r hr)

/-- The factorization recovers the exact original image map. -/
@[reassoc] theorem principalImageMap_ι (r : R) (hr : IsUnit (algebraMap R S r)) :
    principalImageMap R S X r hr ≫ (principalImageOpen R X r).ι = imageMap R S X :=
  IsOpenImmersion.lift_fac _ _ _

/-- Outside the original prime, the canonical branch automatically inverts the scalar. -/
theorem canonicalBranch_isUnit (x : PrimeSpectrum R) (r : R) (hr : r ∉ x.asIdeal) :
    IsUnit (algebraMap R (ScalarPrimeLocalizationCover.Branch x) r) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff _ x.asIdeal r).mpr hr

end FLT.Mazur.FlatScalarImageBaseChange
