/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatTangentNaturality
public import FLT.Mathlib.RingTheory.AugmentationConvolution

/-! # Addition and multiplication on the actual integral cotangents -/

@[expose] public noncomputable section
open WithConv
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K]

omit [PerfectField K] [IsFractionRing R K] in
/-- The zero group morphism has zero cotangent differential. -/
theorem ModelHom.cotangentMap_zero (X Y : FF R K) :
    (ModelHom.zero X Y).cotangentMap = 0 := by
  ext a
  obtain ⟨b, rfl⟩ := Y.cotangentIdeal.toCotangent_surjective a
  rw [← AlgHom.augmentationCotangent_of_mem, ModelHom.cotangentMap_projection]
  change (Bialgebra.counitAlgHom R X.CoordinateRing).augmentationCotangent
    (algebraMap R X.CoordinateRing (Coalgebra.counit (b : Y.CoordinateRing))) = 0
  have hb : Coalgebra.counit (R := R) (b : Y.CoordinateRing) = 0 := b.property
  rw [hb, map_zero, map_zero]

/-- Convolution addition induces addition of the original cotangent maps. -/
theorem ModelHom.cotangentMap_add {X Y : FF R K} (f g : ModelHom X Y) :
    (f.add g).cotangentMap = f.cotangentMap + g.cotangentMap := by
  ext a
  obtain ⟨b, rfl⟩ := Y.cotangentIdeal.toCotangent_surjective a
  rw [← AlgHom.augmentationCotangent_of_mem]
  change (f.add g).cotangentMap _ = f.cotangentMap _ + g.cotangentMap _
  rw [ModelHom.cotangentMap_projection, ModelHom.cotangentMap_projection,
    ModelHom.cotangentMap_projection]
  let d : (Bialgebra.counitAlgHom R X.CoordinateRing).augmentationTangent
      (M := X.Cotangent) :=
    ⟨_, (Bialgebra.counitAlgHom R X.CoordinateRing).augmentationCotangent_mul⟩
  exact AlgHom.augmentationTangent_convolution d f g b

/-- Multiplication by n has differential n on the actual augmentation quotient. -/
theorem FF.cotangentMap_multiply (X : FF R K) (n : ℕ) :
    (X.multiply n).cotangentMap = n • LinearMap.id := by
  induction n with
  | zero =>
    simpa only [FF.multiply, pow_zero, ModelHom.zero, zero_nsmul] using
      ModelHom.cotangentMap_zero X X
  | succ n ih =>
    have he : X.multiply (n + 1) = (X.multiply n).add (BialgHom.id R X.CoordinateRing) := by
      simp only [FF.multiply, ModelHom.add, pow_succ, toConv_ofConv]
    rw [he, ModelHom.cotangentMap_add, ih, ModelHom.cotangentMap_id, add_nsmul, one_nsmul]

/-- Generic annihilation forces the same scalar to kill every integral cotangent. -/
theorem FF.cotangent_nsmul_eq_zero (X : FF R K) (n : ℕ)
    (hn : ∀ x : X.Points, n • x = 0) (a : X.Cotangent) : n • a = 0 := by
  have he := congrArg (fun f : ModelHom X X ↦ f.cotangentMap a)
    ((X.multiply_eq_zero_iff n).mpr hn)
  simpa only [FF.cotangentMap_multiply, ModelHom.cotangentMap_zero,
    LinearMap.zero_apply, LinearMap.smul_apply, LinearMap.id_apply] using he

end ThreeAdicPlan
