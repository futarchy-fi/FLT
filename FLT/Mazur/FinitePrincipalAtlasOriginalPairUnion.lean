/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCoordinates

/-!
# Original image unions recover entire affine intersections

The selected principal overlap coordinates cover exactly the intersection
of the two original affine charts, on either side of the ordered pair.
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

/-- Each original coordinate embedding cuts out exactly its selected scheme open. -/
theorem atlasPrincipalOriginalOpen_image (i : ι) (k : AtlasPrincipalOccurrence U i) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (principalOccurrenceOriginalOpen (dst := D) (a := AA) (b := BB) E i k).opensRange =
      (U i).2.fromSpec ⁻¹ᵁ (atlasPrincipalOpen U (D i k)).1 := by
  intro _ _
  let _ : IsOpenImmersion (U i).2.fromSpec := (U i).2.isOpenImmersion_fromSpec
  rw [← Scheme.Hom.preimage_image_eq (U i).2.fromSpec
    (principalOccurrenceOriginalOpen (dst := D) (a := AA) (b := BB) E i k).opensRange,
    ← Scheme.Hom.opensRange_comp]
  simp only [atlasPrincipalEquiv_incidence, affineOpenUnitChart_opensRange]

/-- Left occurrence images cover the whole original pair intersection. -/
theorem atlasPrincipalOriginalPair_cover_left (i t : ι) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (⨆ p : atlasPrincipalPairs U i t,
      (principalOccurrenceOriginalOpen (dst := D) (a := AA) (b := BB) E i
        ⟨t, .inl p⟩).opensRange) = (U i).2.fromSpec ⁻¹ᵁ (U t).1 := by
  intro _ _
  let _ : IsOpenImmersion (U i).2.fromSpec := (U i).2.isOpenImmersion_fromSpec
  simp_rw [atlasPrincipalOriginalOpen_image U f]
  change (⨆ p : atlasPrincipalPairs U i t,
    (U i).2.fromSpec ⁻¹ᵁ X.basicOpen p.val.1) = _
  have htop := Scheme.Hom.preimage_opensRange (U i).2.fromSpec
  rw [(U i).2.opensRange_fromSpec] at htop
  rw [← Scheme.Hom.preimage_iSup, atlasPrincipalPairs_cover, Scheme.Hom.preimage_inf,
    htop]
  exact inf_eq_right.mpr le_top

/-- Right occurrence images cover the same original pair intersection in the other chart. -/
theorem atlasPrincipalOriginalPair_cover_right (i t : ι) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (⨆ p : atlasPrincipalPairs U i t,
      (principalOccurrenceOriginalOpen (dst := D) (a := AA) (b := BB) E t
        ⟨i, .inr p⟩).opensRange) = (U t).2.fromSpec ⁻¹ᵁ (U i).1 := by
  intro _ _
  let _ : IsOpenImmersion (U t).2.fromSpec := (U t).2.isOpenImmersion_fromSpec
  simp_rw [atlasPrincipalOriginalOpen_image U f]
  change (⨆ p : atlasPrincipalPairs U i t,
    (U t).2.fromSpec ⁻¹ᵁ X.basicOpen p.val.1) = _
  have htop := Scheme.Hom.preimage_opensRange (U t).2.fromSpec
  rw [(U t).2.opensRange_fromSpec] at htop
  rw [← Scheme.Hom.preimage_iSup, atlasPrincipalPairs_cover, Scheme.Hom.preimage_inf,
    htop]
  exact inf_eq_left.mpr le_top

end FLT.Mazur.Approximation
