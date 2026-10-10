/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonPinchingDiagram

/-!
# Reversing the ordered endpoints of the projective line

Exchange the two original affine charts. This gives an involution over the
base field, including exact equalities for both marked sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
universe u
variable (K : Type u) [Field K]

/-- The inverse-coordinate transition also glues the charts in opposite order. -/
theorem endpointReversal_overlap :
    overlapLeft K ≫ right K = overlapRight K ≫ left K := by
  have hi : (inversion K).hom ≫ (inversion K).hom = 𝟙 _ :=
    (inversion K).hom_inv_id
  calc
    overlapLeft K ≫ right K = (inversion K).hom ≫ overlapRight K ≫ right K := by
      simp only [overlapRight, ← Category.assoc, hi, Category.id_comp]
    _ = (inversion K).hom ≫ overlapLeft K ≫ left K := by rw [overlap_condition]
    _ = overlapRight K ≫ left K := by rw [overlapRight, Category.assoc]

/-- The global reciprocal coordinate map, defined on both complete affine charts. -/
def endpointReversal : scheme K ⟶ scheme K :=
  pushout.desc (right K) (left K) (endpointReversal_overlap K)

@[reassoc (attr := simp)] theorem left_endpointReversal :
    left K ≫ endpointReversal K = right K := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem right_endpointReversal :
    right K ≫ endpointReversal K = left K := pushout.inr_desc _ _ _

/-- Reversing the complete charts twice is the identity on the scheme. -/
theorem endpointReversal_involutive : endpointReversal K ≫ endpointReversal K = 𝟙 _ := by
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    simp only [left_endpointReversal_assoc, right_endpointReversal, Category.comp_id]
  · change right K ≫ _ = right K ≫ _
    simp only [right_endpointReversal_assoc, left_endpointReversal, Category.comp_id]

/-- Reversal is an isomorphism of the entire projective line. -/
def endpointReversalIso : scheme K ≅ scheme K where
  hom := endpointReversal K
  inv := endpointReversal K
  hom_inv_id := endpointReversal_involutive K
  inv_hom_id := endpointReversal_involutive K

/-- The involution preserves the original field structure. -/
@[reassoc (attr := simp)] theorem endpointReversal_toBase :
    endpointReversal K ≫ toBase K = toBase K := by
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    simp only [left_endpointReversal_assoc, right_toBase, left_toBase]
  · change right K ≫ _ = right K ≫ _
    simp only [right_endpointReversal_assoc, left_toBase, right_toBase]

/-- Zero is sent to the original infinity section. -/
@[reassoc (attr := simp)] theorem zero_endpointReversal :
    zero K ≫ endpointReversal K = infinity K := by
  rw [zero, Category.assoc, left_endpointReversal]
  rfl

/-- Infinity is sent to the original zero section. -/
@[reassoc (attr := simp)] theorem infinity_endpointReversal :
    infinity K ≫ endpointReversal K = zero K := by
  rw [infinity, Category.assoc, right_endpointReversal]
  rfl

/-- The same involution in schemes over the base field. -/
def endpointReversalOverIso : PolygonPinching.component K ≅ PolygonPinching.component K :=
  Over.isoMk (endpointReversalIso K) (endpointReversal_toBase K)

/-- The ordered sections are exchanged as morphisms over the field. -/
@[reassoc (attr := simp)] theorem zeroSection_endpointReversal :
    zeroSection K ≫ (endpointReversalOverIso K).hom = infinitySection K := by
  apply Over.OverMorphism.ext
  exact zero_endpointReversal K

/-- The opposite ordered section is likewise exchanged over the field. -/
@[reassoc (attr := simp)] theorem infinitySection_endpointReversal :
    infinitySection K ≫ (endpointReversalOverIso K).hom = zeroSection K := by
  apply Over.OverMorphism.ext
  exact infinity_endpointReversal K

end FLT.Mazur.ProjectiveLine
