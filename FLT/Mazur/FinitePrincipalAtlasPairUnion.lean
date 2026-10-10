/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCoherentStage
public import FLT.Mazur.PrincipalOccurrenceAmbientUnion

/-!
# Ambient image unions of actual finite affine atlas intersections

The selected common principal opens of any pair of original affine charts
construct isomorphic full unions in the two finite ambient stages. The
coherent atlas stage supplies every equation used in this construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalOccurrenceLocalComparisonLeft
  principalOccurrenceLocalComparisonRight principalOccurrenceCrossEquationTransport
  principalOccurrencePatchOpen principalOccurrenceCrossOuterLeft principalOccurrenceCrossOuterRight
  principalOccurrenceOpenAt relationIdeal chartAlgebra principalRepresentative
  principalOccurrenceStagePreorder

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} (U : ι → X.affineOpens) (f : X ⟶ Spec R) [LocallyOfFiniteType f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f
local notation "OccurrenceStage" =>
  PrincipalOccurrenceStage D AA BB (fun i k ↦ AlgEquiv.toAlgHom (E i k))

/-- Actual selected overlaps identify their two full finite ambient image unions. -/
def finitePrincipalAtlasPairUnionIso :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    (y : OccurrenceStage) → (hy : ∀ i k, Function.Bijective (y.hom i k)) →
    finitePrincipalAtlasRoutes U f y hy → ∀ i t,
      (@openImageUnion _ _ _ (fun p : atlasPrincipalPairs U i t ↦
        principalOccurrenceOpenAt (dst := D) (a := AA) (b := BB) E y hy (j := ⟨i, t, p⟩) i
          ⟨t, .inl p⟩ rfl) (fun p : atlasPrincipalPairs U i t ↦
        principalOccurrenceOpenAt_isOpenImmersion (dst := D) (a := AA) (b := BB)
          E y hy i ⟨t, .inl p⟩ rfl)).toScheme ≅
      (@openImageUnion _ _ _ (fun p : atlasPrincipalPairs U i t ↦
        principalOccurrenceOpenAt (dst := D) (a := AA) (b := BB) E y hy (j := ⟨i, t, p⟩) t
          ⟨i, .inr p⟩ rfl) (fun p : atlasPrincipalPairs U i t ↦
        principalOccurrenceOpenAt_isOpenImmersion (dst := D) (a := AA) (b := BB)
          E y hy t ⟨i, .inr p⟩ rfl)).toScheme := by
  intro _ _ _ _ y hy he i t
  exact principalOccurrenceAmbientUnionIso (dst := D) (a := AA) (b := BB) E y hy he
    (fun p : atlasPrincipalPairs U i t ↦ ⟨i, t, p⟩) i t
    (fun p ↦ ⟨t, .inl p⟩) (fun p ↦ ⟨i, .inr p⟩) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Each actual selected overlap is retained by the isomorphism of full ambient unions. -/
@[reassoc] theorem finitePrincipalAtlasPairUnionIso_fac :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (y : OccurrenceStage) (hy : ∀ i k, Function.Bijective (y.hom i k))
      (he : finitePrincipalAtlasRoutes U f y hy) (i t : ι) (p : atlasPrincipalPairs U i t),
      @openImageUnionMap _ _ _ (fun p : atlasPrincipalPairs U i t ↦
        principalOccurrenceOpenAt (dst := D) (a := AA) (b := BB) E y hy (j := ⟨i, t, p⟩) i
          ⟨t, .inl p⟩ rfl) (fun p : atlasPrincipalPairs U i t ↦
        principalOccurrenceOpenAt_isOpenImmersion (dst := D) (a := AA) (b := BB)
          E y hy i ⟨t, .inl p⟩ rfl) p ≫ (finitePrincipalAtlasPairUnionIso U f y hy he i t).hom =
      @openImageUnionMap _ _ _ (fun p : atlasPrincipalPairs U i t ↦
        principalOccurrenceOpenAt (dst := D) (a := AA) (b := BB) E y hy (j := ⟨i, t, p⟩) t
          ⟨i, .inr p⟩ rfl) (fun p : atlasPrincipalPairs U i t ↦
        principalOccurrenceOpenAt_isOpenImmersion (dst := D) (a := AA) (b := BB)
          E y hy t ⟨i, .inr p⟩ rfl) p := by
  intro _ _ _ _ y hy he i t p
  exact principalOccurrenceAmbientUnionIso_fac (dst := D) (a := AA) (b := BB) E y hy he
    (fun p : atlasPrincipalPairs U i t ↦ ⟨i, t, p⟩) i t
    (fun p ↦ ⟨t, .inl p⟩) (fun p ↦ ⟨i, .inr p⟩) (fun _ ↦ rfl) (fun _ ↦ rfl) p

end FLT.Mazur.Approximation
