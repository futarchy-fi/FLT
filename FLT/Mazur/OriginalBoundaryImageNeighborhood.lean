/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarImageLocalGeometry
public import FLT.Mazur.OriginalBoundaryFlatImageGeometry

/-!
# Original boundary image points and their neighborhoods

The closure of the actual original boundary image supplies a unique point
of its exact scalar image. Geometry on any neighborhood of that point
transfers to the whole canonical branch, including the full boundary equations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange FlatScalarImageBaseChange
open SchemeScalarPrincipalNeighborhood SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A) [IsAffine A] (J : A.IdealSheafData)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
local instance neighborhoodBoundaryAffine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
set_option quotPrecheck false
local notation "b₀" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "σ" => scalarMorphism (Subring.subtype R)

omit [IsAffine A] in
/-- The full original boundary map has precisely the original boundary support image. -/
theorem originalBoundary_scalar_range : Set.range b₀ = σ '' (J.support : Set A) := by
  have hj := scalarMorphism_natural J.subschemeι (originalBoundaryMap (p := p) (q := q) J) rfl
  rw [← hj]
  change Set.range (σ ∘ J.subschemeι) = _
  rw [Set.range_comp, J.range_subschemeι]

/-- Original boundary image closure constructs its unique exact-image point. -/
theorem originalBoundary_existsUnique_image_point (x : PrimeSpectrum R)
    (hx : x ∈ closure (σ '' (J.support : Set A))) :
    ∃! y : Spec (.of (Scalars b₀)), inclusion b₀ y = x := by
  apply existsUnique_image_point b₀ x
  rwa [originalBoundary_scalar_range p q J]

variable (x : PrimeSpectrum (invariants p.appTop.hom q.appTop.hom))
  (y : Spec (.of (Scalars (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))))
  (hyx : inclusion (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))) y = x)
  (U : (Spec (.of (Scalars (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))))).Opens)
  (hy : y ∈ U)
local notation "L" => ScalarPrimeLocalizationCover.Branch x
local notation "b₁" => base R L J.subscheme

include hyx hy in
/-- Flatness and coverage near the original image point suffice for exact branch descent. -/
theorem originalBoundary_image_faithfullyFlat_of_neighborhood
    [Flat ((projection b₀) ∣_ U)] [Surjective ((projection b₀) ∣_ U)] :
    (RingHom.kerLift (scalarMap b₁)).FaithfullyFlat := by
  let _ : IsAffine (baseChange R L J.subscheme) := by
    unfold baseChange
    infer_instance
  exact (image_faithfullyFlat_iff b₁).mpr
    ⟨projection_property_of_neighborhood R J.subscheme x y hyx U hy (@Flat) inferInstance,
      projection_property_of_neighborhood R J.subscheme x y hyx U hy
        (@Surjective) inferInstance⟩

include hyx hy in
/-- Local integral image geometry supplies branch coverage as well as faithful flatness. -/
theorem originalBoundary_image_faithfullyFlat_of_integral_neighborhood
    [Flat ((projection b₀) ∣_ U)] [IsIntegralHom ((projection b₀) ∣_ U)] :
    (RingHom.kerLift (scalarMap b₁)).FaithfullyFlat := by
  let _ := projection_property_of_neighborhood R J.subscheme x y hyx U hy
    (@Flat) inferInstance
  let _ := projection_property_of_neighborhood R J.subscheme x y hyx U hy
    (@IsIntegralHom) inferInstance
  let _ : IsAffine (baseChange R L J.subscheme) := by
    unfold baseChange
    infer_instance
  let _ : IsIntegralHom b₁ := by
    rw [← projection_inclusion b₁]
    infer_instance
  exact image_faithfullyFlat_of_flat_integral_morphism b₁

end FLT.Mazur.EquivalenceRelationOrderedFrames
