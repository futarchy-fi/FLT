/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOriginalPairUnion
public import FLT.Mazur.PrincipalOccurrenceCommonRecovery

/-!
# Original canonical common unions are actual atlas intersections

All literal common occurrences lie in both original charts. The selected
pair cover is a subfamily, so the canonical union is the entire intersection.
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

/-- An original embedding with a fixed literal label recovers that actual open. -/
theorem atlasPrincipalOriginalOpenAt_image {j : AtlasPrincipalOverlap U}
    (i : ι) (k : AtlasPrincipalOccurrence U i) (hk : D i k = j) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (principalOccurrenceOriginalOpenAt (dst := D) (a := AA) (b := BB) E i k hk).opensRange =
      (U i).2.fromSpec ⁻¹ᵁ (atlasPrincipalOpen U j).1 := by
  intro _ _
  subst j
  exact atlasPrincipalOriginalOpen_image U f i k

/-- The canonical common union is exactly the intersection in the original affine chart. -/
theorem atlasPrincipalOriginalCommonUnion_eq (i t : ι) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    principalOccurrenceOriginalCommonUnion (dst := D) (a := AA) (b := BB) E i t =
      (U i).2.fromSpec ⁻¹ᵁ (U t).1 := by
  intro _ _
  change (⨆ p : PrincipalOccurrenceCommon D i t,
    (principalOccurrenceOriginalOpenAt (dst := D) (a := AA) (b := BB) E
      i p.2.1.val p.2.1.property).opensRange) = _
  apply le_antisymm
  · apply iSup_le
    intro p
    rw [atlasPrincipalOriginalOpenAt_image U f]
    apply Scheme.Hom.preimage_mono
    rw [← p.2.2.property]
    exact atlasPrincipalOpen_le_occurrence U t p.2.2.val
  · rw [← atlasPrincipalOriginalPair_cover_left U f i t]
    apply iSup_le
    intro p
    exact le_iSup_of_le ⟨⟨i, t, p⟩, ⟨⟨t, .inl p⟩, rfl⟩, ⟨⟨i, .inr p⟩, rfl⟩⟩ le_rfl

end FLT.Mazur.Approximation
