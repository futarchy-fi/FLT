/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCommonRecovery
public import FLT.Mazur.OpenImmersionCommonCover

/-!
# Literal original overlap covers of atlas intersections

The canonical common occurrences give a scheme cover of each actual
intersection, so compatibility can be checked on the literal overlaps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv chartAlgebra principalRepresentative

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} (U : ι → X.affineOpens) (f : X ⟶ Spec R)

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f

/-- Both original common embeddings agree in the original scheme. -/
theorem atlasPrincipalOriginalCommon_incidence (i t : ι)
    (p : PrincipalOccurrenceCommon D i t) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    principalOccurrenceOriginalCommonLeft (dst := D) (a := AA) (b := BB) E i t p ≫
        (U i).2.fromSpec =
      principalOccurrenceOriginalCommonLeft (dst := D) (a := AA) (b := BB) E t i
        (principalOccurrenceCommonSwap D i t p) ≫ (U t).2.fromSpec := by
  intro _ _
  exact (principalOccurrenceOriginalOpenAt_atlas (dst := D) (a := AA) (b := BB) E
    (fun i ↦ (U i).2.fromSpec) (fun j ↦ affineOpenUnitChart f (atlasPrincipalOpen U j))
    (atlasPrincipalEquiv_incidence U f) i p.2.1.val p.2.1.property).trans
      (principalOccurrenceOriginalOpenAt_atlas (dst := D) (a := AA) (b := BB) E
        (fun i ↦ (U i).2.fromSpec) (fun j ↦ affineOpenUnitChart f (atlasPrincipalOpen U j))
        (atlasPrincipalEquiv_incidence U f) t p.2.2.val p.2.2.property).symm

/-- Compatibility on all common occurrences implies compatibility on the whole intersection. -/
theorem atlasPrincipalOriginalCommon_compatible (i t : ι) {T : Scheme.{u}}
    (g : Spec Γ(X, (U i).1) ⟶ T) (h : Spec Γ(X, (U t).1) ⟶ T) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (∀ p : PrincipalOccurrenceCommon D i t,
      principalOccurrenceOriginalCommonLeft (dst := D) (a := AA) (b := BB) E i t p ≫ g =
        principalOccurrenceOriginalCommonLeft (dst := D) (a := AA) (b := BB) E t i
          (principalOccurrenceCommonSwap D i t p) ≫ h) →
      pullback.fst (U i).2.fromSpec (U t).2.fromSpec ≫ g =
        pullback.snd (U i).2.fromSpec (U t).2.fromSpec ≫ h := by
  intro _ _ hgh
  let _ := (U i).2.isOpenImmersion_fromSpec
  let _ := (U t).2.isOpenImmersion_fromSpec
  let _ : ∀ p : PrincipalOccurrenceCommon D i t,
      IsOpenImmersion (principalOccurrenceOriginalCommonLeft
        (dst := D) (a := AA) (b := BB) E i t p) :=
    fun p ↦ principalOccurrenceOriginalCommonLeft_isOpenImmersion
      (dst := D) (a := AA) (b := BB) E i t p
  have hc : (⨆ p : PrincipalOccurrenceCommon D i t,
      (principalOccurrenceOriginalCommonLeft (dst := D) (a := AA) (b := BB) E i t p).opensRange) =
      (U i).2.fromSpec ⁻¹ᵁ (U t).2.fromSpec.opensRange := by
    rw [(U t).2.opensRange_fromSpec]
    exact atlasPrincipalOriginalCommonUnion_eq U f i t
  refine openImmersionCommonCover_hom_ext (U i).2.fromSpec (U t).2.fromSpec
    (principalOccurrenceOriginalCommonLeft (dst := D) (a := AA) (b := BB) E i t)
    (fun p ↦ principalOccurrenceOriginalCommonLeft (dst := D) (a := AA) (b := BB) E t i
      (principalOccurrenceCommonSwap D i t p))
    (atlasPrincipalOriginalCommon_incidence U f i t) hc _ _ ?_
  intro p
  erw [openImmersionCommonMap_fst_assoc, openImmersionCommonMap_snd_assoc]
  exact hgh p

end FLT.Mazur.Approximation
