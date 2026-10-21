/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarImageProjection
public import FLT.Mazur.SchemeScalarImageFaithfulGeometry
public import FLT.Mazur.OriginalBoundaryScalarImageLift

/-!
# Exact original-boundary image geometry on flat scalar branches

The whole original closed boundary has its exact scalar image extended
cartesianly to every flat branch. Flatness of the original image projection
and closedness of its range construct faithful flatness on these branches.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange
open SchemeScalarPrincipalNeighborhood SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A) [IsAffine A] (J : A.IdealSheafData)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
local instance boundaryImageAffine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
  [Module.Flat (invariants p.appTop.hom q.appTop.hom) S]
set_option quotPrecheck false
local notation "b₀" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "b₁" => base R S J.subscheme

/-- All original boundary image equations extend exactly on the full scalar branch. -/
theorem originalBoundaryImage_equations :
    equations b₁ = (equations b₀).map (algebraMap R S) :=
  FlatScalarImageEquations.equations_eq_original_map R S J.subscheme

/-- The full original boundary image projection is cartesian on every flat branch. -/
theorem originalBoundaryImageProjection_isPullback :
    IsPullback (source R S J.subscheme) (projection b₁) (projection b₀)
      (FlatScalarImageBaseChange.imageMap R S J.subscheme) :=
  FlatScalarImageBaseChange.projection_isPullback R S J.subscheme

/-- Original image flatness extends to the actual full-boundary branch projection. -/
theorem originalBoundaryImageProjection_flat [Flat (projection b₀)] : Flat (projection b₁) :=
  FlatScalarImageBaseChange.projection_flat_of_original R S J.subscheme

/-- Original image etaleness extends to the actual full-boundary branch projection. -/
theorem originalBoundaryImageProjection_etale [Etale (projection b₀)] : Etale (projection b₁) :=
  FlatScalarImageBaseChange.projection_etale_of_original R S J.subscheme

/-- Closed original image supplies coverage on every entire flat branch. -/
theorem originalBoundaryImageProjection_surjective (hc : IsClosed (Set.range b₀)) :
    Surjective (projection b₁) := by
  let _ := projection_surjective_of_isClosed_range b₀ hc
  exact FlatScalarImageBaseChange.projection_surjective_of_original R S J.subscheme

/-- The original flat closed image constructs faithful flatness of the exact branch kernel. -/
theorem originalBoundaryImage_faithfullyFlat [Flat (projection b₀)]
    (hc : IsClosed (Set.range b₀)) : (RingHom.kerLift (scalarMap b₁)).FaithfullyFlat := by
  let _ : IsAffine (baseChange R S J.subscheme) := by
    unfold baseChange
    infer_instance
  exact (image_faithfullyFlat_iff b₁).mpr
    ⟨originalBoundaryImageProjection_flat p q J S,
      originalBoundaryImageProjection_surjective p q J S hc⟩

/-- Fixed original image geometry leaves only full relation domination for scalar descent. -/
theorem originalBoundary_scalar_of_original_flat_image (hJ : J.comap p = J.comap q)
    [Flat (projection b₀)] (hc : IsClosed (Set.range b₀))
    [Epi (originalBoundaryKernelComparison p q J hJ S)]
    (t : SchemeEffectiveEpiSections.compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ s : S, scalarMap b₁ s = (source R S J.subscheme).appTop t.val := by
  let _ : IsAffine (baseChange R S J.subscheme) := by
    unfold baseChange
    infer_instance
  exact originalBoundary_scalar_of_image p q J hJ S
    (originalBoundaryImage_faithfullyFlat p q J S hc) t

end FLT.Mazur.EquivalenceRelationOrderedFrames
