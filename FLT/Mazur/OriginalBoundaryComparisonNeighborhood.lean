/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarComparisonImageNeighborhood
public import FLT.Mazur.OriginalBoundaryImageNeighborhood
public import FLT.Mazur.OriginalBoundaryEtaleImageLift

/-!
# Original boundary comparison geometry from original image neighborhoods

Construct the original full comparison and its image coordinate. Local
comparison properties transfer to the canonical branch, and an etale image
neighborhood plus local comparison coverage supplies effective domination.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange SchemeScalarImageQuotient
open SchemeScalarPrincipalNeighborhood FlatScalarImageBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))

/-- The original full boundary relation compares to the original scalar kernel pair. -/
def originalBoundaryComparison : pullback p J.subschemeι ⟶ pullback f f :=
  pullback.lift (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ)
    (originalBoundary_scalar_condition p q J hJ)

/-- The original kernel pair has a canonical coordinate in the exact original image. -/
def originalBoundaryKernelImage : pullback f f ⟶ Spec (.of (Scalars f)) :=
  pullback.fst f f ≫ projection f

variable [IsAffine A]
local instance comparisonBoundaryAffine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
variable (x : PrimeSpectrum (invariants p.appTop.hom q.appTop.hom))
  (y : Spec (.of (Scalars (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))))
  (hyx : inclusion (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))) y = x)
  (U : (Spec (.of (Scalars (scalarMorphism
    (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))))).Opens)
  (hy : y ∈ U)
local notation "L" => ScalarPrimeLocalizationCover.Branch x

include hyx hy in
/-- Original comparison geometry near the actual image point controls the entire branch. -/
theorem originalBoundaryComparison_property_of_neighborhood (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange]
    (hP : P ((originalBoundaryComparison p q J hJ) ∣_
      ((originalBoundaryKernelImage p q J) ⁻¹ᵁ U))) :
    P (originalBoundaryKernelComparison p q J hJ L) :=
  FlatScalarComparisonImageNeighborhood.comparison_property R J.subscheme x y hyx U hy
    (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ)
    (originalBoundary_scalar_condition p q J hJ) P hP

include hyx hy in
/-- Etale image geometry and local original comparison coverage give full effective domination. -/
theorem originalBoundaryComparison_effectiveEpi_of_neighborhood [Etale p]
    [Etale ((projection f) ∣_ U)]
    [Surjective ((originalBoundaryComparison p q J hJ) ∣_
      ((originalBoundaryKernelImage p q J) ⁻¹ᵁ U))] :
    EffectiveEpi (originalBoundaryKernelComparison p q J hJ L) := by
  let _ := projection_property_of_neighborhood R J.subscheme x y hyx U hy
    (@Etale) inferInstance
  let _ := originalBoundaryComparison_property_of_neighborhood p q J hJ x y hyx U hy
    (@Surjective) inferInstance
  exact originalBoundaryKernelComparison_effectiveEpi p q J hJ L

include hyx hy in
/-- Local flat comparison coverage also gives domination without etale image geometry. -/
theorem originalBoundaryComparison_epi_of_flat_neighborhood
    [Flat ((originalBoundaryComparison p q J hJ) ∣_
      ((originalBoundaryKernelImage p q J) ⁻¹ᵁ U))]
    [Surjective ((originalBoundaryComparison p q J hJ) ∣_
      ((originalBoundaryKernelImage p q J) ⁻¹ᵁ U))] :
    Epi (originalBoundaryKernelComparison p q J hJ L) := by
  let _ := originalBoundaryComparison_property_of_neighborhood p q J hJ x y hyx U hy
    (@Flat) inferInstance
  let _ := originalBoundaryComparison_property_of_neighborhood p q J hJ x y hyx U hy
    (@Surjective) inferInstance
  exact Flat.epi_of_flat_of_surjective _

end FLT.Mazur.EquivalenceRelationOrderedFrames
