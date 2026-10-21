/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationScalarComparisonNeighborhood
public import FLT.Mazur.FlatScalarImageLocalGeometry

/-!
# Full comparisons over original image neighborhoods

The canonical branch kernel pair factors through the preimage of every
neighborhood of its original image point. This constructs the base map for
local comparison geometry, without choosing or assuming a covering branch.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FlatScalarComparisonImageNeighborhood
open FlatScalarSchemeBaseChange FlatScalarImageBaseChange SchemeScalarImageQuotient
open SchemeRelationScalarBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (X : Scheme.{0}) [Algebra R Γ(X, ⊤)]
  [CompactSpace X] [QuasiSeparatedSpace X] (x : PrimeSpectrum R)
set_option quotPrecheck false
local notation "L" => ScalarPrimeLocalizationCover.Branch x
local notation "f" =>
  SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤))
local notation "c" => projection (base R L X)
local notation "u" => pullback.fst f f
variable (y : Spec (.of (Scalars
    (SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤))))))
  (hyx : inclusion (SchemeScalarPrincipalNeighborhood.scalarMorphism
    (algebraMap R Γ(X, ⊤))) y = x)
  (U : (Spec (.of (Scalars
    (SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤)))))).Opens)
  (hy : y ∈ U)

/-- Original and branch kernel-pair maps have the same exact image coordinate. -/
@[reassoc] theorem kernelOriginal_image :
    kernelOriginal f (algebraMap R L) ≫ u ≫ projection f =
      pullback.fst c c ≫ c ≫ imageMap R L X := by
  rw [kernelOriginal_first_assoc, projection_imageMap]
  rfl

/-- The whole branch kernel pair factors through the original image neighborhood preimage. -/
def kernelNeighborhood : pullback c c ⟶ ((u ≫ projection f) ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict (u ≫ projection f) U).lift
    (pullback.fst c c ≫ c ≫ localImageMap R X x y hyx U hy)
    (kernelOriginal f (algebraMap R L)) (by
      rw [Category.assoc, Category.assoc, localImageMap_ι]
      exact (kernelOriginal_image R X x).symm)

/-- The neighborhood factor retains the full original kernel pair. -/
@[reassoc] theorem kernelNeighborhood_ι :
    kernelNeighborhood R X x y hyx U hy ≫ ((u ≫ projection f) ⁻¹ᵁ U).ι =
      kernelOriginal f (algebraMap R L) :=
  (isPullback_morphismRestrict (u ≫ projection f) U).lift_snd _ _ _

variable {D : Scheme.{0}} (a b : D ⟶ X)
  (h : a ≫ SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤)) =
    b ≫ SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤)))

include hyx hy in
/-- Local geometry of the original full comparison transfers to the canonical branch. -/
theorem comparison_property (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange]
    (hP : P ((pullback.lift a b h) ∣_ ((u ≫ projection f) ⁻¹ᵁ U))) :
    P (kernelComparison a b f h (algebraMap R L)) :=
  kernelComparison_property_of_neighborhood a b f h (algebraMap R L)
    ((u ≫ projection f) ⁻¹ᵁ U) (kernelNeighborhood R X x y hyx U hy)
    (kernelNeighborhood_ι R X x y hyx U hy) P hP

end FLT.Mazur.FlatScalarComparisonImageNeighborhood
