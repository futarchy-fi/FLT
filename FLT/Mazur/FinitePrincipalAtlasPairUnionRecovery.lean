/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOriginalPairUnion
public import FLT.Mazur.PrincipalOccurrenceAmbientUnionRecovery

/-!
# Recovering full pair intersections from finite ambient unions

The two image unions used for a selected ordered pair recover the whole
original intersection in their respective affine charts. This is an exact
inverse-image statement, valid at every bijective occurrence stage.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv chartAlgebra relationIdeal

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

/-- The left finite image union recovers the entire original chart intersection. -/
theorem finitePrincipalAtlasPair_preimage_left :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (y : OccurrenceStage) (hy : ∀ i k, Function.Bijective (y.hom i k)) (i t : ι),
      principalOccurrenceAmbientProjection (dst := D) (a := AA) (b := BB) E y i ⁻¹ᵁ
        (⨆ p : atlasPrincipalPairs U i t,
          (principalOccurrenceOpen y hy i ⟨t, .inl p⟩).opensRange) =
        (U i).2.fromSpec ⁻¹ᵁ (U t).1 := by
  intro _ _ _ _ y hy i t
  rw [Scheme.Hom.preimage_iSup]
  calc
    _ = ⨆ p : atlasPrincipalPairs U i t,
        (principalOccurrenceOriginalOpen (dst := D) (a := AA) (b := BB) E i
          ⟨t, .inl p⟩).opensRange := by
      apply iSup_congr
      intro p
      exact principalOccurrenceOpenAt_preimage (dst := D) (a := AA) (b := BB)
        E y hy i ⟨t, .inl p⟩ rfl
    _ = _ := atlasPrincipalOriginalPair_cover_left U f i t

/-- The right finite image union recovers the entire original chart intersection. -/
theorem finitePrincipalAtlasPair_preimage_right :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (y : OccurrenceStage) (hy : ∀ i k, Function.Bijective (y.hom i k)) (i t : ι),
      principalOccurrenceAmbientProjection (dst := D) (a := AA) (b := BB) E y t ⁻¹ᵁ
        (⨆ p : atlasPrincipalPairs U i t,
          (principalOccurrenceOpen y hy t ⟨i, .inr p⟩).opensRange) =
        (U t).2.fromSpec ⁻¹ᵁ (U i).1 := by
  intro _ _ _ _ y hy i t
  rw [Scheme.Hom.preimage_iSup]
  calc
    _ = ⨆ p : atlasPrincipalPairs U i t,
        (principalOccurrenceOriginalOpen (dst := D) (a := AA) (b := BB) E t
          ⟨i, .inr p⟩).opensRange := by
      apply iSup_congr
      intro p
      exact principalOccurrenceOpenAt_preimage (dst := D) (a := AA) (b := BB)
        E y hy t ⟨i, .inr p⟩ rfl
    _ = _ := atlasPrincipalOriginalPair_cover_right U f i t

end FLT.Mazur.Approximation
