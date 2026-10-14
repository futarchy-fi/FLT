/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationEtaleBranchPropagation

/-!
# Constructing a split monic seed from a two-sided etale branch

Base change the coefficient target by the actual seed coefficient morphism.
Its graph is an etale section of the complete pulled-back source. Thus the
monic-seed requirement is constructed after this explicit etale base change.
No claim that base change repairs missing orbit coverage is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeSplitEtaleSourceSeed
set_option backward.isDefEq.respectTransparency false
variable {A T Z : Scheme.{u}} (w : A ⟶ T) (a : Z ⟶ A)

/-- The complete original source pulled back by the seed's coefficient morphism. -/
def source : Scheme.{u} := pullback w (a ≫ w)

/-- The unchanged source coordinate. -/
def toSource : source w a ⟶ A := pullback.fst w (a ≫ w)

/-- The projection to the newly chosen coefficient target. -/
def projection : source w a ⟶ Z := pullback.snd w (a ≫ w)

/-- The seed graph is constructed on the full scheme, without reducing its target. -/
def seed : Z ⟶ source w a := pullback.lift a (𝟙 Z) (Category.id_comp _).symm

@[reassoc]
theorem seed_toSource : seed w a ≫ toSource w a = a := pullback.lift_fst _ _ _

@[reassoc]
theorem seed_projection : seed w a ≫ projection w a = 𝟙 Z := pullback.lift_snd _ _ _

/-- This really is a base change of the unrestricted source, retaining all its fibers. -/
theorem isPullback : IsPullback (toSource w a) (projection w a) w (a ≫ w) :=
  IsPullback.of_hasPullback w (a ≫ w)

/-- The actual original seed point is retained. -/
theorem seed_point (z : Z) : toSource w a (seed w a z) = a z :=
  congrArg (fun t ↦ t z) (seed_toSource w a)

instance seed_mono : Mono (seed w a) :=
  mono_of_mono_fac (seed_projection w a)

instance toSource_etale [Etale (a ≫ w)] : Etale (toSource w a) :=
  inferInstanceAs (Etale (pullback.fst w (a ≫ w)))

/-- Both original etale properties construct an etale graph into the complete new source. -/
instance seed_etale [Etale a] [Etale (a ≫ w)] : Etale (seed w a) := by
  let _ : Etale (seed w a ≫ toSource w a) := by rw [seed_toSource]; infer_instance
  exact Etale.of_comp (seed w a) (toSource w a)

/-- Over the new coefficient target the seed is literally the identity, hence open and monic. -/
instance seed_target_isOpenImmersion : IsOpenImmersion (seed w a ≫ projection w a) := by
  rw [seed_projection]
  infer_instance

end FLT.Mazur.SchemeSplitEtaleSourceSeed
