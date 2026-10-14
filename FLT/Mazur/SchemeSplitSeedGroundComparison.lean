/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeSplitEtaleSourceSeed
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Comparing coefficient split sources with actual ground changes

The complete coefficient pullback maps canonically to the complete ground
pullback. Its scheme-valued tests are exactly the ground tests whose two
old coefficient morphisms agree. No flatness or reducedness is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeSplitSeedGroundComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T A Z : Scheme.{u}} (w : A ⟶ T) (i : T ⟶ S) (a : Z ⟶ A)

/-- The actual ground-changed source, with all coefficient fibers retained. -/
def groundSource : Scheme.{u} := pullback (w ≫ i) ((a ≫ w) ≫ i)

/-- The original parameter coordinate of the ground change. -/
def groundToSource : groundSource w i a ⟶ A := pullback.fst _ _

/-- The new ground coordinate, retained independently from the old coefficients. -/
def groundProjection : groundSource w i a ⟶ Z := pullback.snd _ _

/-- Coefficient equality gives a canonical map into the actual ground change. -/
def comparison : SchemeSplitEtaleSourceSeed.source w a ⟶ groundSource w i a :=
  pullback.mapDesc w (a ≫ w) i

@[reassoc]
theorem comparison_source : comparison w i a ≫ groundToSource w i a =
    SchemeSplitEtaleSourceSeed.toSource w a := by
  simp only [comparison, groundToSource, pullback.lift_fst, Category.comp_id,
    SchemeSplitEtaleSourceSeed.toSource]

@[reassoc]
theorem comparison_projection : comparison w i a ≫ groundProjection w i a =
    SchemeSplitEtaleSourceSeed.projection w a := by
  simp only [comparison, groundProjection, pullback.lift_snd, Category.comp_id,
    SchemeSplitEtaleSourceSeed.projection]

instance comparison_mono : Mono (comparison w i a) := by
  constructor
  intro Y x y h
  apply pullback.hom_ext
  · simpa only [Category.assoc, comparison_source, SchemeSplitEtaleSourceSeed.toSource] using
      congrArg (fun g ↦ g ≫ groundToSource w i a) h
  · simpa only [Category.assoc, comparison_projection, SchemeSplitEtaleSourceSeed.projection] using
      congrArg (fun g ↦ g ≫ groundProjection w i a) h

/-- A ground test lifts precisely when its two full coefficient morphisms coincide. -/
theorem existsUnique_lift_iff {Y : Scheme.{u}} (b : Y ⟶ groundSource w i a) :
    (∃! t : Y ⟶ SchemeSplitEtaleSourceSeed.source w a, t ≫ comparison w i a = b) ↔
      b ≫ groundToSource w i a ≫ w = b ≫ groundProjection w i a ≫ a ≫ w := by
  constructor
  · rintro ⟨t, rfl, _⟩
    simp only [Category.assoc, comparison_source_assoc, comparison_projection_assoc]
    exact congrArg (fun g ↦ t ≫ g) (pullback.condition (f := w) (g := a ≫ w))
  · intro h
    let t := pullback.lift (b ≫ groundToSource w i a) (b ≫ groundProjection w i a)
      (by simpa only [Category.assoc] using h)
    have ht : t ≫ comparison w i a = b := by
      apply pullback.hom_ext
      · simp only [Category.assoc, comparison, pullback.lift_fst, Category.comp_id,
          t, groundToSource]
      · simp only [Category.assoc, comparison, pullback.lift_snd, Category.comp_id,
          t, groundProjection]
    exact ⟨t, ht, fun y hy ↦ (cancel_mono (comparison w i a)).mp (hy.trans ht.symm)⟩

/-- Over a separated coefficient model the comparison is closed, not assumed open. -/
instance comparison_isClosedImmersion [IsSeparated i] :
    IsClosedImmersion (comparison w i a) :=
  inferInstanceAs (IsClosedImmersion (pullback.mapDesc w (a ≫ w) i))

/-- The original seed defines the diagonal section in the complete ground source. -/
def groundSeed : Z ⟶ groundSource w i a :=
  pullback.lift a (𝟙 Z) (by simp only [Category.assoc, Category.id_comp])

@[reassoc]
theorem seed_comparison : SchemeSplitEtaleSourceSeed.seed w a ≫ comparison w i a =
    groundSeed w i a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, comparison, SchemeSplitEtaleSourceSeed.seed,
      groundSeed, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, comparison, SchemeSplitEtaleSourceSeed.seed,
      groundSeed, pullback.lift_snd, Category.comp_id]

end FLT.Mazur.SchemeSplitSeedGroundComparison
