/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAdmissibleMapUnique

/-!
# Faithful evaluation determines the full admissible change

Equality of the two actual evaluated coordinate formulas recovers all
four parameters. This criterion retains arbitrary nilpotent scalars and
does not divide by either residue characteristic two or three.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type*} [CommRing R] [CommRing A]
  (W V : WeierstrassCurve R) (φ : R →+* A) (e : Coordinate W 2 →+* A)
  (he : Function.Injective e) (hφ : ∀ r, e (algebraMap R _ r) = φ r)
  (C D : VariableChange R) (hC : C • V = W) (hD : D • V = W)

include he hφ hC hD

/-- The two retained coordinate values determine the whole admissible change uniquely. -/
theorem evaluatedVariableChange_unique
    (hx : φ (C.u : R) ^ 2 * e (coord W 2 0) + φ C.r =
      φ (D.u : R) ^ 2 * e (coord W 2 0) + φ D.r)
    (hy : φ (C.u : R) ^ 3 * e (coord W 2 1) +
        φ (C.u : R) ^ 2 * φ C.s * e (coord W 2 0) + φ C.t =
      φ (D.u : R) ^ 3 * e (coord W 2 1) +
        φ (D.u : R) ^ 2 * φ D.s * e (coord W 2 0) + φ D.t) : C = D := by
  apply affineVariableChangeMap_injective W V C D hC hD
  apply hom_ext
  intro i
  fin_cases i
  · change affineVariableChangeMap V W C hC (coord V 2 0) =
      affineVariableChangeMap V W D hD (coord V 2 0)
    apply he
    simpa only [affineVariableChangeMap_x, map_add, map_mul, map_pow, hφ] using hx
  · change affineVariableChangeMap V W C hC (coord V 2 1) =
      affineVariableChangeMap V W D hD (coord V 2 1)
    apply he
    simpa only [affineVariableChangeMap_y, map_add, map_mul, map_pow, hφ] using hy
  · change affineVariableChangeMap V W C hC (coord V 2 2) =
      affineVariableChangeMap V W D hD (coord V 2 2)
    simp only [coord_self, map_one]

end FLT.Mazur.WeierstrassIntegralChart
