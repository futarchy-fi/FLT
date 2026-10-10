/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOriginalCovers
public import FLT.Mazur.PrincipalOccurrenceTargetChartGluing

/-!
# Actual finite-stage target maps from arbitrary affine atlases

The original scheme supplies finite occurrence data, coordinate equivalences,
incidence, finite-type algebras, and the constrained cover inclusions. These
inputs construct actual glued maps without requesting any atlas cover data
or comparison equations from the caller.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} [Finite ι] (U : ι → X.affineOpens) (f : X ⟶ Spec R) [LocallyOfFiniteType f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, Subtype.val (atlasPrincipalOpen U j)))
local notation "E" => atlasPrincipalEquiv U f
local notation "OccurrenceStage" =>
  PrincipalOccurrenceStage D AA BB (fun i k ↦ AlgEquiv.toAlgHom (E i k))

/-- Original finite affine atlases construct glued target maps at a common bijective stage. -/
theorem exists_finitePrincipalAtlas_target_gluing :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (s : ∀ i, Finset (relationIdeal R Γ(X, (U i).1)))
      (t : AtlasPrincipalOverlap U → ι),
      (∀ j, (atlasPrincipalOpen U j).1 ≤ (U (t j)).1) →
      ∃ y : OccurrenceStage, ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          ∃ g : ∀ j, Spec (.of (PrincipalStage R Γ(X, (atlasPrincipalOpen U j).1)
              (BB j) (y.target j))) ⟶ Spec (.of (Stage R Γ(X, (U (t j)).1) (y.source (t j)))),
            ∀ j (p : PrincipalOccurrencePatchTo (dst := D) j (t j)),
              principalOccurrencePatchOpen y hy p.1 ≫ g j =
                principalOccurrenceTargetPatchMap (dst := D) (a := AA) (b := BB)
                  E y hy (t j) p := by
  intro _ _ _ _ x s t ht
  let _ : ∀ i, IsOpenImmersion (U i).2.fromSpec :=
    fun i ↦ (U i).2.isOpenImmersion_fromSpec
  exact exists_principalOccurrence_target_chart_gluing (dst := D) (a := AA) (b := BB)
    E x t (atlasPrincipalIncoming U)
    (fun j ↦ atlasPrincipal_original_target_cover U f j.1 (t j)
      ⟨j.2.1, .inl j.2.2⟩ (ht j))
    (fun i ↦ (U i).2.fromSpec) (fun j ↦ affineOpenUnitChart f (atlasPrincipalOpen U j))
    (atlasPrincipalEquiv_incidence U f) s

end FLT.Mazur.Approximation
