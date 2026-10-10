/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOriginalCovers
public import FLT.Mazur.PrincipalOccurrenceAtlasCoverEquations

/-!
# Persistent target-compatible covers from actual affine atlases

The original scheme supplies its target-compatible patch covers. They
descend to a common bijective occurrence stage and remain covers at every
later bijective stage, without extra original cover hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalOccurrencePatchOpen relationIdeal

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

/-- Target-compatible atlas patch covers persist above one bijective stage. -/
theorem exists_finitePrincipalAtlas_cover_stage :
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
        (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∀ z : OccurrenceStage, y ≤ z →
          ∀ hz : ∀ i k, Function.Bijective (z.hom i k), ∀ j,
            (⨆ p : PrincipalOccurrencePatchTo (dst := D) j (t j),
              (principalOccurrencePatchOpen z hz p.1).opensRange) = ⊤ := by
  intro _ _ _ _ x s t ht
  obtain ⟨y, hxy, hs, hy, hc⟩ :=
    exists_principalOccurrence_patch_covers (dst := D) (a := AA) (b := BB) E x
      (fun j (p : PrincipalOccurrencePatchTo (dst := D) j (t j)) ↦ p.1)
      (fun j ↦ atlasPrincipal_original_patches_cover U f j (t j) (ht j)) s
  refine ⟨y, hxy, hs, hy, fun z hyz hz j ↦ ?_⟩
  exact principalOccurrencePatchCover_of_le (dst := D) (a := AA) (b := BB) E y hy hyz hz
    (fun p : PrincipalOccurrencePatchTo (dst := D) j (t j) ↦ p.1) (hc j)

end FLT.Mazur.Approximation
