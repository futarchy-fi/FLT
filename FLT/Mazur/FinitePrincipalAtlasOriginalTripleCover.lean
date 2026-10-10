/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOriginalCovers
public import FLT.Mazur.PrincipalOccurrenceOriginalImageComparison

/-!
# Original triple patches covered through the other pair of charts

If the inner overlap occurs in a second chart and the outer overlap in a
third, their intersection is covered by the chosen second-to-third overlaps.
This supplies genuine original geometry for finite-union descent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} (U : ι → X.affineOpens) (f : X ⟶ Spec R)

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f

/-- A triple patch is covered using the selected overlaps between the other two charts. -/
theorem atlasPrincipal_original_triple_cover
    (j : AtlasPrincipalOverlap U) (p : PrincipalOccurrencePatch (dst := D) j)
    (t : ι) (k : AtlasPrincipalOccurrence U t) (hk : D t k = j)
    (r : ι) (l : AtlasPrincipalOccurrence U r) (hl : D r l = D p.1.val.1 p.2) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (principalOccurrenceOriginalPatchOpen (dst := D) (a := AA) (b := BB) E p).opensRange ≤
      ⨆ m : atlasPrincipalPairs U t r,
        (principalOccurrenceOriginalPatchOpen (dst := D) (a := AA) (b := BB) E
          ⟨⟨⟨t, k⟩, hk⟩, ⟨r, .inl m⟩⟩).opensRange := by
  intro _ _
  let _ : ∀ i, IsOpenImmersion (U i).2.fromSpec :=
    fun i ↦ (U i).2.isOpenImmersion_fromSpec
  let _ : ∀ j, IsOpenImmersion (affineOpenUnitChart f (atlasPrincipalOpen U j)) :=
    fun j ↦ affineOpenUnitChart_isOpenImmersion f (atlasPrincipalOpen U j)
  simp only [principalOccurrenceOriginalPatch_image_atlas (dst := D) (a := AA) (b := BB)
    E (fun i ↦ (U i).2.fromSpec)
    (fun j ↦ affineOpenUnitChart f (atlasPrincipalOpen U j)) (atlasPrincipalEquiv_incidence U f),
    affineOpenUnitChart_opensRange]
  change affineOpenUnitChart f (atlasPrincipalOpen U j) ⁻¹ᵁ
      (atlasPrincipalOpen U (D p.1.val.1 p.2)).1 ≤
    ⨆ m : atlasPrincipalPairs U t r,
      affineOpenUnitChart f (atlasPrincipalOpen U j) ⁻¹ᵁ X.basicOpen m.val.1
  rw [← Scheme.Hom.preimage_iSup, atlasPrincipalPairs_cover]
  intro z hz
  refine ⟨?_, ?_⟩
  · have hj : (atlasPrincipalOpen U j).1 ≤ (U t).1 := by
      rw [← hk]
      exact atlasPrincipalOpen_le_occurrence U t k
    apply hj
    have hz' : affineOpenUnitChart f (atlasPrincipalOpen U j) z ∈
        (affineOpenUnitChart f (atlasPrincipalOpen U j)).opensRange := ⟨z, rfl⟩
    simpa only [affineOpenUnitChart_opensRange] using hz'
  · have hl' : (atlasPrincipalOpen U (D p.1.val.1 p.2)).1 ≤ (U r).1 := by
      rw [← hl]
      exact atlasPrincipalOpen_le_occurrence U r l
    exact hl' hz

end FLT.Mazur.Approximation
