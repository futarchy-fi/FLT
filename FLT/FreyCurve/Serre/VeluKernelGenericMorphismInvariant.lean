/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluTranslationFieldCoordinates

/-!
# Kernel invariance of the actual generic Vélu morphism

The translation action fixes every original target affine function, hence
fixes the actual generic scheme morphism into the original Vélu target cubic.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  {u v : K} (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G)

include hQG

/-- Every original target affine function is fixed by the original kernel translation. -/
theorem translationFieldHom_veluChart :
    (translationFieldHom E hQ).comp (veluGenericChart E G hodd) =
      veluGenericChart E G hodd := by
  have h := translationFieldHom_velu E hQ G hodd hQG
  apply hom_ext
  intro i
  fin_cases i
  · change translationFieldHom E hQ (veluGenericChart E G hodd
      (coord (curve E G) 2 0)) = veluGenericChart E G hodd (coord (curve E G) 2 0)
    simpa only [veluGenericChart_x] using h.1
  · change translationFieldHom E hQ (veluGenericChart E G hodd
      (coord (curve E G) 2 1)) = veluGenericChart E G hodd (coord (curve E G) 2 1)
    simpa only [veluGenericChart_y] using h.2
  · change translationFieldHom E hQ (veluGenericChart E G hodd
      (coord (curve E G) 2 2)) = veluGenericChart E G hodd (coord (curve E G) 2 2)
    rw [coord_self, map_one, map_one]

/-- Kernel translation preserves the original generic map as an actual scheme morphism. -/
@[reassoc] theorem translationFieldHom_veluMorphism :
    Spec.map (CommRingCat.ofHom (translationFieldHom E hQ).toRingHom) ≫
        veluGenericMorphism E G hodd = veluGenericMorphism E G hodd := by
  rw [veluGenericMorphism, ← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom
    ((translationFieldHom E hQ).comp (veluGenericChart E G hodd)).toRingHom) ≫ _ = _
  rw [translationFieldHom_veluChart E G hodd hQ hQG]

end WeierstrassCurve.Velu
