/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarImageBaseChange
public import FLT.Mazur.SchemeScalarImageGeometry

/-!
# Geometric base change of the full image projection

The projection to the exact scalar image itself forms a cartesian square.
Thus its etaleness, flatness, integrality and coverage extend to every flat
scalar branch without reconstructing image geometry branch by branch.
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

/-- The new image projection retains the original geometric projection. -/
@[reassoc] theorem projection_imageMap :
    projection b₁ ≫ imageMap R S X = source R S X ≫ projection b₀ := by
  apply (cancel_mono (inclusion b₀)).mp
  rw [Category.assoc, (image_isPullback R S X).w, ← Category.assoc,
    projection_inclusion, Category.assoc, projection_inclusion]
  exact (square R S X).w.symm

/-- Flat scalar extension commutes with the full image projection itself. -/
theorem projection_isPullback : IsPullback (source R S X) (projection b₁)
    (projection b₀) (imageMap R S X) := by
  apply IsPullback.of_bot _ (projection_imageMap R S X).symm (image_isPullback R S X)
  simpa only [projection_inclusion] using square R S X

/-- Etaleness of the original image projection holds on every full flat branch. -/
theorem projection_etale_of_original [Etale (projection b₀)] : Etale (projection b₁) :=
  MorphismProperty.of_isPullback (projection_isPullback R S X) inferInstance

/-- Flatness of the original image projection holds on every full flat branch. -/
theorem projection_flat_of_original [Flat (projection b₀)] : Flat (projection b₁) :=
  MorphismProperty.of_isPullback (projection_isPullback R S X) inferInstance

/-- Coverage of the exact original image covers every exact flat branch image. -/
theorem projection_surjective_of_original [Surjective (projection b₀)] :
    Surjective (projection b₁) :=
  MorphismProperty.of_isPullback (projection_isPullback R S X) inferInstance

/-- Integral full image geometry is preserved on every flat branch. -/
theorem projection_integral_of_original [IsIntegralHom (projection b₀)] :
    IsIntegralHom (projection b₁) :=
  MorphismProperty.of_isPullback (projection_isPullback R S X) inferInstance

/-- Finite full image geometry is preserved on every flat branch. -/
theorem projection_finite_of_original [IsFinite (projection b₀)] : IsFinite (projection b₁) :=
  MorphismProperty.of_isPullback (projection_isPullback R S X) inferInstance

end FLT.Mazur.FlatScalarImageBaseChange
