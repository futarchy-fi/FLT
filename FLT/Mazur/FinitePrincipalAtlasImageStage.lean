/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOriginalCovers
public import FLT.Mazur.PrincipalOccurrenceCoherentRefinement
public import FLT.Mazur.PrincipalOccurrenceAtlasImageRefinement

/-!
# Image descent for actual finite affine atlases

Actual atlas incidence supplies every original patch image inclusion.
All inclusions of outer opens persist as patch-image inclusions on a
common tail of bijective occurrence stages.
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

/-- The chosen geometric atlas supplies all patch-image inclusions on one refinement tail. -/
theorem exists_finitePrincipalAtlas_image_stage :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (s : ∀ i, Finset (relationIdeal R Γ(X, (U i).1))),
      ∃ y : OccurrenceStage, ∃ _hxy : x ≤ y, s ≤ y.source ∧
        (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∀ z : OccurrenceStage, y ≤ z →
          ∀ hz : ∀ i k, Function.Bijective (z.hom i k), ∀ j
            (p q : PrincipalOccurrencePatch (dst := D) j),
            (atlasPrincipalOpen U (D p.1.val.1 p.2)).1 ≤
              (atlasPrincipalOpen U (D q.1.val.1 q.2)).1 →
            (principalOccurrencePatchOpen z hz p).opensRange ≤
              (principalOccurrencePatchOpen z hz q).opensRange := by
  intro _ _ _ _ x s
  let _ : ∀ i, IsOpenImmersion (U i).2.fromSpec :=
    fun i ↦ (U i).2.isOpenImmersion_fromSpec
  let _ : ∀ j, IsOpenImmersion (affineOpenUnitChart f (atlasPrincipalOpen U j)) :=
    fun j ↦ affineOpenUnitChart_isOpenImmersion f (atlasPrincipalOpen U j)
  obtain ⟨y, hxy, hs, hy, hinc⟩ :=
    exists_principalOccurrence_atlas_image_inclusions (dst := D) (a := AA) (b := BB) E x
      (fun i ↦ (U i).2.fromSpec) (fun j ↦ affineOpenUnitChart f (atlasPrincipalOpen U j))
      (atlasPrincipalEquiv_incidence U f) s
  refine ⟨y, hxy, hs, hy, fun z hyz hz j p q h ↦ hinc z hyz hz j p q ?_⟩
  simpa only [affineOpenUnitChart_opensRange] using h

end FLT.Mazur.Approximation
