/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleInputOpen
public import FLT.Mazur.WeierstrassInfinityTripleScalarMaps

/-!
# Regularity of the three original infinity inputs

Each actual point map factors as an open restriction followed by a flat
projection of the infinity input triple. Stalkwise regularity therefore applies
to the genuine full member without assuming that member is affine.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The three original point maps into the infinity chart, in input order. -/
def infinityTripleInputMorphism (i : Fin 3) :
    InfinityTripleFull W hΔ ⟶ Spec (.of (Coordinate W 1)) :=
  ![infinityTripleFullFirst W hΔ ≫
      Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom),
    infinityTripleFullFirst W hΔ ≫
      Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom),
    infinityTripleFullLast W hΔ ≫
      Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom)] i

/-- Every original input map on the actual full member is flat. -/
instance infinityTripleInputMorphism_flat (i : Fin 3) :
    Flat (infinityTripleInputMorphism W hΔ i) := by
  fin_cases i
  · change Flat (infinityTripleFullFirst W hΔ ≫ _)
    rw [← infinityTripleFullInputChart_first]
    infer_instance
  · change Flat (infinityTripleFullFirst W hΔ ≫ _)
    rw [← infinityTripleFullInputChart_second]
    infer_instance
  · change Flat (infinityTripleFullLast W hΔ ≫ _)
    rw [← infinityTripleFullInputChart_third]
    infer_instance

/-- These scheme maps induce exactly the three previously defined scalar inputs. -/
theorem infinityTripleInputMorphism_sections (i : Fin 3) :
    specSectionHom (infinityTripleInputMorphism W hΔ i) =
      (infinityTripleScalarPoint W hΔ (i.castAdd 4)).toRingHom := by
  fin_cases i
  · change specSectionHom (infinityTripleFullFirst W hΔ ≫
      Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom)) = _
    rw [specSectionHom_comp]
    rfl
  · change specSectionHom (infinityTripleFullFirst W hΔ ≫
      Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom)) = _
    rw [specSectionHom_comp]
    rfl
  · change specSectionHom (infinityTripleFullLast W hΔ ≫
      Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom)) = _
    rw [specSectionHom_comp]
    rfl

/-- The original Z coordinates are regular in the actual full intersection's section ring. -/
theorem infinityTripleScalarZ_input_regular (i : Fin 3) :
    IsRegular (infinityTripleScalarZ W hΔ (i.castAdd 4)) := by
  have h := specSectionHom_isRegular (infinityTripleInputMorphism W hΔ i)
    (infinityChart_coord_z_regular W)
  rw [infinityTripleInputMorphism_sections] at h
  exact h

end FLT.Mazur.WeierstrassIntegralChart
