/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleSystem
public import FLT.Mathlib.RingTheory.AugmentationCotangent

/-! # Cotangents of the original finite-flat models and their integral morphisms -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- The actual augmentation ideal of the chosen integral coordinate algebra. -/
abbrev FF.cotangentIdeal (X : FF R K) :=
  RingHom.ker (Bialgebra.counitAlgHom R X.CoordinateRing)

/-- The cotangent module at the identity of the original finite-flat model. -/
abbrev FF.Cotangent (X : FF R K) := X.cotangentIdeal.Cotangent

/-- The actual Hopf coordinate map preserves the augmentation ideal. -/
theorem ModelHom.cotangentIdeal_le {X Y : FF R K} (f : ModelHom X Y) :
    Y.cotangentIdeal ≤ X.cotangentIdeal.comap f.toAlgHom := by
  intro a ha
  change Bialgebra.counitAlgHom R X.CoordinateRing (f a) = 0
  exact (CoalgHomClass.counit_comp_apply f a).trans ha

/-- The map on cotangents is induced by the original contravariant coordinate map. -/
def ModelHom.cotangentMap {X Y : FF R K} (f : ModelHom X Y) :
    Y.Cotangent →ₗ[R] X.Cotangent :=
  Ideal.mapCotangent _ _ f.toAlgHom f.cotangentIdeal_le

/-- On actual augmentation representatives this is the original coordinate map. -/
theorem ModelHom.cotangentMap_mk {X Y : FF R K} (f : ModelHom X Y)
    (a : Y.cotangentIdeal) :
    f.cotangentMap (Y.cotangentIdeal.toCotangent a) =
      X.cotangentIdeal.toCotangent ⟨f a, f.cotangentIdeal_le a.property⟩ := rfl

/-- Identity of actual models induces identity on their cotangents. -/
theorem ModelHom.cotangentMap_id (X : FF R K) :
    ModelHom.cotangentMap (X := X) (Y := X) (BialgHom.id R X.CoordinateRing) = LinearMap.id := by
  ext a
  obtain ⟨b, rfl⟩ := X.cotangentIdeal.toCotangent_surjective a
  rfl

/-- Composition retains the contravariant order of original coordinate maps. -/
theorem ModelHom.cotangentMap_comp {X Y Z : FF R K}
    (f : ModelHom X Y) (g : ModelHom Y Z) :
    ModelHom.cotangentMap (X := X) (Y := Z) (f.comp g) = f.cotangentMap.comp g.cotangentMap := by
  ext a
  obtain ⟨b, rfl⟩ := Z.cotangentIdeal.toCotangent_surjective a
  rfl

/-- Closed integral immersions give surjective cotangent transition maps. -/
theorem ModelHom.cotangentMap_surjective {X Y : FF R K} (f : ModelHom X Y)
    (hf : Function.Surjective f) : Function.Surjective f.cotangentMap := by
  intro a
  obtain ⟨b, rfl⟩ := X.cotangentIdeal.toCotangent_surjective a
  obtain ⟨c, hc⟩ := hf b
  have hzero : c ∈ Y.cotangentIdeal := by
    change Bialgebra.counitAlgHom R Y.CoordinateRing c = 0
    exact (CoalgHomClass.counit_comp_apply f c).symm.trans
      ((congrArg (Bialgebra.counitAlgHom R X.CoordinateRing) hc).trans b.property)
  refine ⟨Y.cotangentIdeal.toCotangent ⟨c, hzero⟩, ?_⟩
  rw [ModelHom.cotangentMap_mk]
  congr 1
  exact Subtype.ext hc

end ThreeAdicPlan
