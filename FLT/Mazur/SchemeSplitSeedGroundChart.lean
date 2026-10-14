/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeSplitSeedGroundFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Actual ground charts and the coefficient constraint inside them

An open parameter chart remains open after ground change. Its coefficient
split source immerses into that actual chart, with both the old parameter
and new ground coordinate preserved. Openness of this immersion is not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeSplitSeedGroundComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T A Z H : Scheme.{u}} (w : A ⟶ T) (i : T ⟶ S) (a : Z ⟶ A)
  (k : A ⟶ H) (j : H ⟶ S) (hk : w ≫ i = k ≫ j)

/-- The genuine ground change of the original parameter scheme. -/
def groundParameter : Scheme.{u} := pullback j ((a ≫ w) ≫ i)

/-- The open original parameter chart, pulled back by the actual ground morphism. -/
def groundChart : groundSource w i a ⟶ groundParameter w i a j :=
  pullback.lift (groundToSource w i a ≫ k) (groundProjection w i a) (by
    rw [Category.assoc, ← hk]
    exact pullback.condition)

@[reassoc]
theorem groundChart_old : groundChart w i a k j hk ≫ pullback.fst j ((a ≫ w) ≫ i) =
    groundToSource w i a ≫ k := pullback.lift_fst _ _ _

@[reassoc]
theorem groundChart_new : groundChart w i a k j hk ≫ pullback.snd j ((a ≫ w) ≫ i) =
    groundProjection w i a := pullback.lift_snd _ _ _

/-- This is a base change of the original chart, with the whole ground fiber retained. -/
theorem groundChart_isPullback : IsPullback (groundToSource w i a)
    (groundChart w i a k j hk) k (pullback.fst j ((a ≫ w) ≫ i)) := by
  have h : IsPullback (groundToSource w i a)
      (groundChart w i a k j hk ≫ pullback.snd j ((a ≫ w) ≫ i))
      (k ≫ j) ((a ≫ w) ≫ i) := by
    rw [groundChart_new, ← hk]
    exact IsPullback.of_hasPullback (w ≫ i) ((a ≫ w) ≫ i)
  exact h.of_bot (groundChart_old w i a k j hk).symm (IsPullback.of_hasPullback _ _)

instance groundChart_isOpenImmersion [IsOpenImmersion k] :
    IsOpenImmersion (groundChart w i a k j hk) :=
  MorphismProperty.of_isPullback (groundChart_isPullback w i a k j hk) inferInstance

/-- The coefficient split source maps to the actual changed parameter scheme. -/
def splitChart : SchemeSplitEtaleSourceSeed.source w a ⟶ groundParameter w i a j :=
  comparison w i a ≫ groundChart w i a k j hk

@[reassoc]
theorem splitChart_old : splitChart w i a k j hk ≫ pullback.fst j ((a ≫ w) ≫ i) =
    SchemeSplitEtaleSourceSeed.toSource w a ≫ k := by
  rw [splitChart, Category.assoc, groundChart_old, comparison_source_assoc]

@[reassoc]
theorem splitChart_new : splitChart w i a k j hk ≫ pullback.snd j ((a ≫ w) ≫ i) =
    SchemeSplitEtaleSourceSeed.projection w a := by
  rw [splitChart, Category.assoc, groundChart_new, comparison_projection]

/-- The scheme map to the actual ground parameter chart is an immersion. -/
instance splitChart_isImmersion [IsSeparated i] [IsOpenImmersion k] :
    IsImmersion (splitChart w i a k j hk) :=
  inferInstanceAs (IsImmersion (comparison w i a ≫ groundChart w i a k j hk))

/-- The split source keeps the old parameter value and the literal new ground point. -/
theorem splitChart_seed_point (z : Z) :
    (splitChart w i a k j hk ≫ pullback.fst j ((a ≫ w) ≫ i))
        (SchemeSplitEtaleSourceSeed.seed w a z) = k (a z) ∧
    (splitChart w i a k j hk ≫ pullback.snd j ((a ≫ w) ≫ i))
        (SchemeSplitEtaleSourceSeed.seed w a z) = z := by
  constructor
  · rw [splitChart_old]
    change k (SchemeSplitEtaleSourceSeed.toSource w a
      (SchemeSplitEtaleSourceSeed.seed w a z)) = k (a z)
    rw [SchemeSplitEtaleSourceSeed.seed_point]
  · rw [splitChart_new]
    exact congrArg (fun g ↦ g z) (SchemeSplitEtaleSourceSeed.seed_projection w a)

end FLT.Mazur.SchemeSplitSeedGroundComparison
