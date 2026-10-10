/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasAmpleFiber
public import FLT.Mazur.FiniteAffineLineCover

/-!
# A proper finite-presentation envelope retaining an ample fiber

The envelope extends the specified line and retains ampleness on the chosen
residue fiber. Its closed recovery map is over the identical affine base.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel FLT.Mazur.FCurve

namespace FLT.Mazur.Approximation

universe u

attribute [local irreducible] atlasPrincipalEquiv principalRepresentative

/-- The specified line and its ample fiber extend to a proper finite-presentation envelope. -/
theorem exists_proper_ampleFiber_finitelyPresented_closed_envelope {R : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f] (L : X.Modules)
    (hL : LocallyFreeRankOne L) (s : Spec R)
    (hA : AmpleLineBundle ((Scheme.Modules.pullback (f.fiberι s)).obj L)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec R) (i : X ⟶ Y) (M : Y.Modules),
      IsProper g ∧ LocallyOfFinitePresentation g ∧ IsClosedImmersion i ∧ i ≫ g = f ∧
        LocallyFreeRankOne M ∧ Nonempty ((Scheme.Modules.pullback i).obj M ≅ L) ∧
        AmpleLineBundle ((Scheme.Modules.pullback (g.fiberι s)).obj M) := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : X.IsSeparated := ⟨by
    simpa only [terminal.comp_from] using
      (inferInstance : IsSeparated (f ≫ terminal.from (Spec R)))⟩
  obtain ⟨ι, hι, U₀, hU₀, e, hcover⟩ := hL.finite_affine_trivializing_cover
  let _ := hι
  let U (j : ι) : X.affineOpens := ⟨U₀ j, hU₀ j⟩
  have hU : TopologicalSpace.IsOpenCover (fun j ↦ (U j).1) := hcover
  let _ : ∀ j, Algebra R Γ(X, (U j).1) := fun j ↦ chartAlgebra f (U j)
  let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
    fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
  let _ : ∀ j, Algebra.FiniteType R Γ(X, (U j).1) :=
    fun j ↦ atlasChartAlgebra_finiteType f (U j)
  let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
    fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
  obtain ⟨y, _, hy, M, hM, hrec, ha⟩ :=
    exists_finitePrincipalAtlas_lineSheaf_ample_fiber U f hU L e s hA
    (Classical.choice (finitePrincipalAtlas_gluingStage_nonempty U f))
  let E := atlasPrincipalEquiv U f
  let g := principalOccurrenceGluedStructure (dst := atlasPrincipalDestination U)
    (a := atlasPrincipalSection U) (b := fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))) E y
  exact ⟨_, g, finitePrincipalAtlasProjection U f hU y, M, hy,
    principalOccurrenceGluedStructure_locallyOfFinitePresentation _ y,
    finitePrincipalAtlasProjection_isClosedImmersion U f hU y,
    finitePrincipalAtlasProjection_over U f hU y, hM, hrec, ha⟩

end FLT.Mazur.Approximation
