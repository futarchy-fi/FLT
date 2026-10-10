/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasProper

/-!
# Proper finitely presented closed envelopes over an affine base

Every proper scheme over the original affine base embeds as a closed
subscheme of a proper finitely presented scheme over that same base.
The input morphism is not assumed finitely presented.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

universe u

attribute [local irreducible] atlasPrincipalEquiv principalRepresentative

/-- Proper morphisms to affine schemes have proper finitely presented closed envelopes. -/
theorem exists_proper_finitelyPresented_closed_envelope {R : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec R) (i : X ⟶ Y),
      IsProper g ∧ LocallyOfFinitePresentation g ∧ IsClosedImmersion i ∧ i ≫ g = f := by
  classical
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : X.IsSeparated := ⟨by
    simpa only [terminal.comp_from] using
      (inferInstance : IsSeparated (f ≫ terminal.from (Spec R)))⟩
  obtain ⟨s, hs, htop⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp isCompact_univ
  let _ := hs.to_subtype
  let U (i : s) : X.affineOpens := i.val
  have hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1) := by
    change (⨆ i : s, (U i).1) = ⊤
    simpa only [U, iSup_subtype] using htop.symm
  let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
  let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
    fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
  let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
    fun i ↦ atlasChartAlgebra_finiteType f (U i)
  let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
    fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
  obtain ⟨y, _, hy⟩ := exists_finitePrincipalAtlas_isProper U f hU
    (Classical.choice (finitePrincipalAtlas_gluingStage_nonempty U f))
  let E := atlasPrincipalEquiv U f
  let g := principalOccurrenceGluedStructure (dst := atlasPrincipalDestination U)
    (a := atlasPrincipalSection U) (b := fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))) E y
  refine ⟨_, g, finitePrincipalAtlasProjection U f hU y, hy, ?_,
    finitePrincipalAtlasProjection_isClosedImmersion U f hU y,
    finitePrincipalAtlasProjection_over U f hU y⟩
  exact principalOccurrenceGluedStructure_locallyOfFinitePresentation _ y

end FLT.Mazur.Approximation
