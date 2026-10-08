/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicPolarization
public import FLT.Mazur.WeierstrassInputSwap
public import FLT.Mazur.WeierstrassProjectiveAdditionBoundary

/-!
# Homogeneous addition under input interchange

Interchanging the two points changes every polynomial addition coordinate
by the same unit, minus one. This integral identity is the input to the
comparison of normalized addition morphisms on their principal opens.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The third-intersection representative is antisymmetric in its inputs. -/
theorem thirdIntersection_swap (P Q : Fin 3 → R) :
    thirdIntersection W Q P = -thirdIntersection W P Q := by
  ext i
  simp only [thirdIntersection, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The polynomial addition representative changes by the scalar minus one under swapping. -/
theorem projectiveAdd_swap (P Q : Fin 3 → R) :
    W.toProjective.addXYZ Q P = -W.toProjective.addXYZ P Q := by
  have h (i : Fin 3) := congrFun (thirdIntersection_swap W P Q) i
  simp only [Pi.neg_apply] at h
  ext i
  fin_cases i
  · change W.toProjective.addX Q P = -W.toProjective.addX P Q
    simpa only [thirdIntersection_x] using h 0
  · change W.toProjective.addY Q P = -W.toProjective.addY P Q
    simp only [Projective.addY, Projective.negY_eq,
      ← thirdIntersection_x, ← thirdIntersection_y, ← thirdIntersection_z, h]
    ring
  · change W.toProjective.addZ Q P = -W.toProjective.addZ P Q
    simpa only [thirdIntersection_z] using h 2

/-- Tensor interchange carries the universal output to the negative opposite output. -/
theorem chartProductAdditionCoordinates_swap (j k : Fin 3) (i : Fin 3) :
    chartProductSwap W j k (chartProductAdditionCoordinates W j k i) =
      -chartProductAdditionCoordinates W k j i := by
  have hl : chartProductSwap W j k ∘ chartProductLeft W j k ∘ coord W j =
      chartProductRight W k j ∘ coord W j := by
    funext a
    exact DFunLike.congr_fun (chartProductSwap_left W j k) (coord W j a)
  have hr : chartProductSwap W j k ∘ chartProductRight W j k ∘ coord W k =
      chartProductLeft W k j ∘ coord W k := by
    funext a
    exact DFunLike.congr_fun (chartProductSwap_right W j k) (coord W k a)
  have h := chartProductAdditionCoordinates_map W j k (chartProductSwap W j k)
  rw [hl, hr, projectiveAdd_swap] at h
  exact congrFun h i

end FLT.Mazur.WeierstrassIntegralChart
