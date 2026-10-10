/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCoordinates
public import FLT.Mazur.PrincipalOccurrenceTargetPatchSelection

/-!
# Original occurrence covers supplied by scheme atlases

The finite occurrence atlas now satisfies the precise original chart-cover
inclusion consumed by target-chart gluing. Containment in the target is the
only geometric input; the covering occurrences were already constructed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} (U : ι → X.affineOpens) (f : X ⟶ Spec R)

/-- Pulling back an occurrence open gives precisely its principal spectrum image. -/
theorem atlasPrincipal_occurrence_preimage (i : ι) (k : AtlasPrincipalOccurrence U i) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (U i).2.fromSpec ⁻¹ᵁ (atlasPrincipalOpen U (atlasPrincipalDestination U i k)).1 =
      (principalOccurrenceOriginalOpen (dst := atlasPrincipalDestination U)
        (a := atlasPrincipalSection U) (b := fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1)))
        (atlasPrincipalEquiv U f) i k).opensRange := by
  intro _ _
  rw [principalOccurrenceOriginalOpen_opensRange, ← atlasPrincipalSection_open]
  exact (U i).2.fromSpec_preimage_basicOpen _

/-- Actual original spectrum images satisfy the required target-compatible cover inclusion. -/
theorem atlasPrincipal_original_target_cover (i t : ι) (k : AtlasPrincipalOccurrence U i)
    (h : (atlasPrincipalOpen U (atlasPrincipalDestination U i k)).1 ≤ (U t).1) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (principalOccurrenceOriginalOpen (dst := atlasPrincipalDestination U)
        (a := atlasPrincipalSection U) (b := fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1)))
        (atlasPrincipalEquiv U f) i k).opensRange ≤
      ⨆ l : {l : AtlasPrincipalOccurrence U i //
        ∃ n : AtlasPrincipalOccurrence U t,
          atlasPrincipalDestination U t n = atlasPrincipalDestination U i l},
        (principalOccurrenceOriginalOpen (dst := atlasPrincipalDestination U)
        (a := atlasPrincipalSection U) (b := fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1)))
        (atlasPrincipalEquiv U f) i l.val).opensRange := by
  intro _ _ z hz
  rw [principalOccurrenceOriginalOpen_opensRange,
    ← (U i).2.fromSpec_preimage_basicOpen] at hz
  have hz' := atlasPrincipal_occurrence_target_cover U i t k h hz
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hz'
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨l, ?_⟩
  rw [principalOccurrenceOriginalOpen_opensRange, ← (U i).2.fromSpec_preimage_basicOpen]
  exact hl

/-- Every literal overlap has a canonical incoming occurrence from its first chart. -/
def atlasPrincipalIncoming (j : AtlasPrincipalOverlap U) :
    PrincipalIncoming (dst := atlasPrincipalDestination U) j :=
  ⟨⟨j.1, ⟨j.2.1, .inl j.2.2⟩⟩, rfl⟩

/-- The prescribed target-compatible patch family covers each original overlap. -/
theorem atlasPrincipal_original_patches_cover (j : AtlasPrincipalOverlap U) (t : ι)
    (h : (atlasPrincipalOpen U j).1 ≤ (U t).1) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (⨆ p : PrincipalOccurrencePatchTo (dst := atlasPrincipalDestination U) j t,
      (principalOccurrenceOriginalPatchOpen (dst := atlasPrincipalDestination U)
        (a := atlasPrincipalSection U) (b := fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1)))
        (atlasPrincipalEquiv U f) p.1).opensRange) = ⊤ := by
  intro _ _
  apply principalOccurrenceOriginalPatchTo_cover (dst := atlasPrincipalDestination U)
    (a := atlasPrincipalSection U) (b := fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1)))
    (atlasPrincipalEquiv U f) t
    (atlasPrincipalIncoming U j)
  exact atlasPrincipal_original_target_cover U f j.1 t ⟨j.2.1, .inl j.2.2⟩ h

end FLT.Mazur.Approximation
