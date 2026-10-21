/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarImageNeighborhoodGeometry
public import FLT.Mazur.SchemeScalarImageFaithfulGeometry

/-!
# Faithful flatness from an original image neighborhood

Flatness and coverage of the original restricted image projection construct
faithful flatness of the exact branch coefficients. Alternatively integrality
on that neighborhood supplies coverage, using the exact image equations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FlatScalarImageBaseChange
open FlatScalarSchemeBaseChange SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (X : Scheme.{0}) [IsAffine X] [Algebra R Γ(X, ⊤)]
set_option quotPrecheck false
local notation "b₀" =>
  SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤))
local notation "b₁" => base R S X
variable (r : R) (hr : IsUnit (algebraMap R S r))

include hr in
/-- Original neighborhood flatness and coverage construct faithful exact branch coefficients. -/
theorem image_faithfullyFlat_of_principal
    [Flat ((projection b₀) ∣_ principalImageOpen R X r)]
    [Surjective ((projection b₀) ∣_ principalImageOpen R X r)] :
    (RingHom.kerLift (scalarMap b₁)).FaithfullyFlat := by
  let _ : IsAffine (baseChange R S X) := by
    unfold baseChange
    infer_instance
  exact (image_faithfullyFlat_iff b₁).mpr
    ⟨projection_flat_of_principal R S X r hr,
      projection_surjective_of_principal R S X r hr⟩

include hr in
/-- Local integrality covers the whole exact branch image without a coverage hypothesis. -/
theorem projection_surjective_of_principal_integral
    [IsIntegralHom ((projection b₀) ∣_ principalImageOpen R X r)] :
    Surjective (projection b₁) := by
  let _ := projection_integral_of_principal R S X r hr
  let _ : IsIntegralHom b₁ := by
    rw [← projection_inclusion b₁]
    infer_instance
  exact projection_surjective_of_integral b₁

include hr in
/-- Flat integral original neighborhood geometry constructs faithful branch coefficients. -/
theorem image_faithfullyFlat_of_principal_integral
    [Flat ((projection b₀) ∣_ principalImageOpen R X r)]
    [IsIntegralHom ((projection b₀) ∣_ principalImageOpen R X r)] :
    (RingHom.kerLift (scalarMap b₁)).FaithfullyFlat := by
  let _ : IsAffine (baseChange R S X) := by
    unfold baseChange
    infer_instance
  exact (image_faithfullyFlat_iff b₁).mpr
    ⟨projection_flat_of_principal R S X r hr,
      projection_surjective_of_principal_integral R S X r hr⟩

end FLT.Mazur.FlatScalarImageBaseChange
