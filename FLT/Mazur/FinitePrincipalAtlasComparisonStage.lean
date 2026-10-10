/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOriginalCovers
public import FLT.Mazur.PrincipalOccurrenceCoherentRefinement
public import FLT.Mazur.FinitePrincipalAtlasImageStage

/-!
# Actual comparison stages of finite affine atlases

The finite geometric atlas supplies every comparison equation by incidence.
All actual finite cross-chart routes then agree on a common bijective stage.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalOccurrenceLocalComparisonLeft
  principalOccurrenceLocalComparisonRight principalOccurrenceCrossEquationTransport
  principalOccurrencePatchOpen principalOccurrenceCrossOuterLeft principalOccurrenceCrossOuterRight
  principalOccurrenceOpenAt relationIdeal

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} [Finite ι] (U : ι → X.affineOpens) (f : X ⟶ Spec R) [LocallyOfFiniteType f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f
local notation "OccurrenceStage" =>
  PrincipalOccurrenceStage D AA BB (fun i k ↦ AlgEquiv.toAlgHom (E i k))

/-- All actual routes into every common ambient chart agree. -/
def finitePrincipalAtlasRoutes :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    (y : OccurrenceStage) → (∀ i k, Function.Bijective (y.hom i k)) → Prop := by
  intro _ _ _ _ y hy
  exact
          ∀ j (p q : PrincipalOccurrencePatch (dst := D) j)
            (i : ι) (k l : AtlasPrincipalOccurrence U i)
            (hk : D i k = D p.1.val.1 p.2) (hl : D i l = D q.1.val.1 q.2),
            principalOccurrenceCrossOuterLeft y hy p q ≫
                principalOccurrenceOpenAt (dst := D) (a := AA) (b := BB) E y hy i k hk =
              principalOccurrenceCrossOuterRight y hy p q ≫
                principalOccurrenceOpenAt (dst := D) (a := AA) (b := BB) E y hy i l hl

/-- The original atlas constructs the exhaustive comparison equations at a finite stage. -/
theorem exists_finitePrincipalAtlas_comparison_stage :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (_hx : ∀ i k, Function.Bijective (x.hom i k))
      (s : ∀ i, Finset (relationIdeal R Γ(X, (U i).1))),
      ∃ y : OccurrenceStage, ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k), finitePrincipalAtlasRoutes U f y hy := by
  intro _ _ _ _ x hx s
  let _ : ∀ i, IsOpenImmersion (U i).2.fromSpec :=
    fun i ↦ (U i).2.isOpenImmersion_fromSpec
  exact exists_principalOccurrence_all_atlas_routes (dst := D) (a := AA) (b := BB) E x hx
    (fun i ↦ (U i).2.fromSpec) (fun j ↦ affineOpenUnitChart f (atlasPrincipalOpen U j))
    (atlasPrincipalEquiv_incidence U f) s

end FLT.Mazur.Approximation
