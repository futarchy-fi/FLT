/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInputTriple
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Flat projection to the last two infinity inputs

Reassociate the actual fiber product using its tensor-spectrum comparison.
This identifies the last-pair map with a base change of the first chart's
flat structure map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Replace the tensor spectrum in the input triple by its defining fiber product. -/
def infinityInputTriplePullback : InfinityInputTriple W ⟶
    pullback (pullback.snd (chartStructure W 1) (chartStructure W 1) ≫
      chartStructure W 1) (chartStructure W 1) :=
  pullback.map _ _ _ _ (pullbackSpecIso R (Coordinate W 1) (Coordinate W 1)).inv
    (𝟙 _) (𝟙 _) (by
      dsimp only [chartStructure]
      rw [Category.comp_id, ← Category.assoc, pullbackSpecIso_inv_snd]
      simpa only [chartProductRight, AlgHom.toRingHom_eq_coe] using
        (specAlgHom_base R (chartProductRight W 1 1)).symm)
    (by simp)

/-- The comparison with the nested pullback is an isomorphism. -/
instance infinityInputTriplePullback_isIso : IsIso (infinityInputTriplePullback W) := by
  unfold infinityInputTriplePullback
  infer_instance

/-- The original last-pair projection expressed by reassociation of fiber products. -/
def infinityInputTripleLastPair :
    InfinityInputTriple W ⟶ Spec (.of (ChartProduct W 1 1)) :=
  infinityInputTriplePullback W ≫
    (pullbackAssoc (chartStructure W 1) (chartStructure W 1)
      (chartStructure W 1) (chartStructure W 1)).hom ≫
    pullback.snd _ _ ≫ (pullbackSpecIso R (Coordinate W 1) (Coordinate W 1)).hom

/-- The last-pair projection is flat, since the omitted first chart is base-flat. -/
instance infinityInputTripleLastPair_flat : Flat (infinityInputTripleLastPair W) := by
  unfold infinityInputTripleLastPair
  infer_instance

/-- The first member of the last pair is the original middle input. -/
@[reassoc] theorem infinityInputTripleLastPair_left :
    infinityInputTripleLastPair W ≫
        Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom) =
      infinityInputTripleSecond W := by
  simp [infinityInputTripleLastPair, chartProductLeft, infinityInputTriplePullback,
    infinityInputTripleSecond, infinityInputTriplePair, chartProductRight, chartStructure,
    Algebra.TensorProduct.includeLeft, AlgHom.toRingHom_eq_coe]

/-- The second member of the last pair is the original third input. -/
@[reassoc] theorem infinityInputTripleLastPair_right :
    infinityInputTripleLastPair W ≫
        Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom) =
      infinityInputTripleThird W := by
  have he : Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom) =
      (pullbackSpecIso R (Coordinate W 1) (Coordinate W 1)).inv ≫
        pullback.snd (chartStructure W 1) (chartStructure W 1) := by
    exact (pullbackSpecIso_inv_snd R (Coordinate W 1) (Coordinate W 1)).symm
  rw [he, ← Category.assoc]
  simp [infinityInputTripleLastPair, infinityInputTriplePullback, infinityInputTripleThird]

/-- The two projections jointly detect morphisms into the tensor product chart. -/
theorem infinityProductSpec_hom_ext {X : Scheme.{u}}
    {f g : X ⟶ Spec (.of (ChartProduct W 1 1))}
    (hl : f ≫ Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom))
    (hr : f ≫ Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom)) : f = g := by
  apply (cancel_mono (pullbackSpecIso R (Coordinate W 1) (Coordinate W 1)).inv).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullbackSpecIso_inv_fst,
      chartProductLeft, Algebra.TensorProduct.includeLeft] using hl
  · simpa only [Category.assoc, pullbackSpecIso_inv_snd, chartProductRight,
      AlgHom.toRingHom_eq_coe] using hr

end FLT.Mazur.WeierstrassIntegralChart
