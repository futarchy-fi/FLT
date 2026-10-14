/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeSplitSeedGroundComparison

/-!
# The split source as a scheme fiber of the ground-aware coefficient map

The coefficient target of a ground change is T ×[S] Z. Its section defined
by the seed cuts out exactly A ×[T] Z inside A ×[S] Z. The Cartesian square
is proved on all scheme tests, retaining nilpotents and the Z coordinate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeSplitSeedGroundComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T A Z : Scheme.{u}} (w : A ⟶ T) (i : T ⟶ S) (a : Z ⟶ A)

/-- The coefficient target for the genuine ground change. -/
def groundTarget : Scheme.{u} := pullback i ((a ≫ w) ≫ i)

/-- The full ground source maps to old coefficients together with its new ground coordinate. -/
def groundCoefficients : groundSource w i a ⟶ groundTarget w i a :=
  pullback.lift (groundToSource w i a ≫ w) (groundProjection w i a)
    (by simpa only [Category.assoc, groundToSource, groundProjection] using
      pullback.condition (f := w ≫ i) (g := (a ≫ w) ≫ i))

/-- The seed determines an actual section of the ground-aware coefficient target. -/
def coefficientSection : Z ⟶ groundTarget w i a :=
  pullback.lift (a ≫ w) (𝟙 Z) (Category.id_comp _).symm

@[reassoc]
theorem groundCoefficients_old : groundCoefficients w i a ≫ pullback.fst i ((a ≫ w) ≫ i) =
    groundToSource w i a ≫ w := pullback.lift_fst _ _ _

@[reassoc]
theorem groundCoefficients_new : groundCoefficients w i a ≫ pullback.snd i ((a ≫ w) ≫ i) =
    groundProjection w i a := pullback.lift_snd _ _ _

@[reassoc]
theorem coefficientSection_old : coefficientSection w i a ≫ pullback.fst i ((a ≫ w) ≫ i) =
    a ≫ w := pullback.lift_fst _ _ _

@[reassoc]
theorem coefficientSection_new : coefficientSection w i a ≫ pullback.snd i ((a ≫ w) ≫ i) =
    𝟙 Z := pullback.lift_snd _ _ _

@[reassoc]
theorem comparison_coefficients : comparison w i a ≫ groundCoefficients w i a =
    SchemeSplitEtaleSourceSeed.projection w a ≫ coefficientSection w i a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, groundCoefficients_old, coefficientSection_old,
      comparison_source_assoc]
    exact pullback.condition
  · simp only [Category.assoc, groundCoefficients_new, coefficientSection_new,
      Category.comp_id, comparison_projection]

/-- The whole coefficient split source is the fiber over the constructed coefficient section. -/
theorem comparison_isPullback : IsPullback (comparison w i a)
    (SchemeSplitEtaleSourceSeed.projection w a)
    (groundCoefficients w i a) (coefficientSection w i a) := by
  have h₁ (c : PullbackCone (groundCoefficients w i a) (coefficientSection w i a)) :
      (c.fst ≫ groundToSource w i a) ≫ w = c.snd ≫ (a ≫ w) := by
    simpa only [Category.assoc, groundCoefficients_old, coefficientSection_old] using
      congrArg (fun g ↦ g ≫ pullback.fst i ((a ≫ w) ≫ i)) c.condition
  have h₂ (c : PullbackCone (groundCoefficients w i a) (coefficientSection w i a)) :
      c.fst ≫ groundProjection w i a = c.snd := by
    simpa only [Category.assoc, groundCoefficients_new, coefficientSection_new,
      Category.comp_id] using
      congrArg (fun g ↦ g ≫ pullback.snd i ((a ≫ w) ≫ i)) c.condition
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (comparison_coefficients w i a)
    (fun c ↦ pullback.lift (c.fst ≫ groundToSource w i a) c.snd (h₁ c)) ?_ ?_ ?_)
  · intro c
    apply pullback.hom_ext
    · simp only [Category.assoc, comparison, pullback.lift_fst, Category.comp_id,
        groundToSource]
    · simpa only [Category.assoc, comparison, pullback.lift_snd, Category.comp_id,
        groundProjection] using
        (h₂ c).symm
  · intro c
    exact pullback.lift_snd _ _ _
  · intro c z hz₁ hz₂
    apply pullback.hom_ext
    · simpa only [Category.assoc, comparison_source, SchemeSplitEtaleSourceSeed.toSource,
        pullback.lift_fst] using congrArg (fun g ↦ g ≫ groundToSource w i a) hz₁
    · simpa only [SchemeSplitEtaleSourceSeed.projection, pullback.lift_snd] using hz₂

/-- Separatedness gives the actual closed coefficient section before any source restriction. -/
instance coefficientSection_isClosedImmersion [IsSeparated i] :
    IsClosedImmersion (coefficientSection w i a) := by
  let _ : IsSeparated (pullback.snd i ((a ≫ w) ≫ i)) := inferInstance
  have h : IsClosedImmersion
      (coefficientSection w i a ≫ pullback.snd i ((a ≫ w) ≫ i)) := by
    rw [coefficientSection_new]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd i ((a ≫ w) ≫ i))

end FLT.Mazur.SchemeSplitSeedGroundComparison
