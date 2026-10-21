/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarImagePrincipalFactor
public import FLT.Mazur.FlatScalarImageProjection
public import FLT.Mazur.SchemePullbackThroughOpen

/-!
# Full branch geometry from an original image neighborhood

The whole exact branch projection is the pullback of the original projection
restricted to a principal neighborhood whose scalar is inverted on the branch.
Flatness, etaleness, coverage and integrality therefore need only hold there.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FlatScalarImageBaseChange
open FlatScalarSchemeBaseChange SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (X : Scheme.{0}) [Algebra R Γ(X, ⊤)] [CompactSpace X] [QuasiSeparatedSpace X]
set_option quotPrecheck false
local notation "b₀" =>
  SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤))
local notation "b₁" => base R S X
variable (r : R) (hr : IsUnit (algebraMap R S r))

/-- The branch source lands over the original principal image neighborhood. -/
def principalSourceMap : baseChange R S X ⟶
    ((projection b₀) ⁻¹ᵁ principalImageOpen R X r).toScheme :=
  SchemePullbackThroughOpen.sourceMap (projection_isPullback R S X)
    (principalImageOpen R X r) (principalImageMap R S X r hr)
    (principalImageMap_ι R S X r hr)

/-- The entire branch projection is the pullback of the original restricted projection. -/
theorem principalProjection_isPullback :
    IsPullback (principalSourceMap R S X r hr) (projection b₁)
      ((projection b₀) ∣_ principalImageOpen R X r) (principalImageMap R S X r hr) :=
  SchemePullbackThroughOpen.isPullback (projection_isPullback R S X)
    (principalImageOpen R X r) (principalImageMap R S X r hr)
    (principalImageMap_ι R S X r hr)

include hr in
/-- Flatness on the original neighborhood suffices on the whole branch. -/
theorem projection_flat_of_principal [Flat ((projection b₀) ∣_ principalImageOpen R X r)] :
    Flat (projection b₁) :=
  MorphismProperty.of_isPullback (principalProjection_isPullback R S X r hr) inferInstance

include hr in
/-- Etaleness on the original neighborhood suffices on the whole branch. -/
theorem projection_etale_of_principal [Etale ((projection b₀) ∣_ principalImageOpen R X r)] :
    Etale (projection b₁) :=
  MorphismProperty.of_isPullback (principalProjection_isPullback R S X r hr) inferInstance

include hr in
/-- Coverage on the original neighborhood covers the full branch image. -/
theorem projection_surjective_of_principal
    [Surjective ((projection b₀) ∣_ principalImageOpen R X r)] :
    Surjective (projection b₁) :=
  MorphismProperty.of_isPullback (principalProjection_isPullback R S X r hr) inferInstance

include hr in
/-- Integrality on the original neighborhood suffices on the whole branch. -/
theorem projection_integral_of_principal
    [IsIntegralHom ((projection b₀) ∣_ principalImageOpen R X r)] :
    IsIntegralHom (projection b₁) :=
  MorphismProperty.of_isPullback (principalProjection_isPullback R S X r hr) inferInstance

include hr in
/-- Finiteness on the original neighborhood suffices on the whole branch. -/
theorem projection_finite_of_principal [IsFinite ((projection b₀) ∣_ principalImageOpen R X r)] :
    IsFinite (projection b₁) :=
  MorphismProperty.of_isPullback (principalProjection_isPullback R S X r hr) inferInstance

end FLT.Mazur.FlatScalarImageBaseChange
