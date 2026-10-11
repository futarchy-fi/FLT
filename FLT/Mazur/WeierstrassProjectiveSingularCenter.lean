/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveAdditionChart

/-!
# Polynomial addition at the scheme-theoretic singular center

The original homogeneous formulas send a right input with X = Y = 0 back
to X = Y = 0 when a3, a4 and a6 vanish. This includes the mixed infinity/affine
presentations and works over arbitrary coefficient algebras.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The original homogeneous law preserves the singular origin before normalization. -/
theorem projectiveAdd_singular_origin (P Q : Fin 3 → R)
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    (hx : Q 0 = 0) (hy : Q 1 = 0) :
    W.toProjective.addXYZ P Q 0 = 0 ∧ W.toProjective.addXYZ P Q 1 = 0 := by
  simp only [Projective.addXYZ, Projective.addX, Projective.addY, Projective.addZ,
    Projective.negAddY, Projective.negY, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, WeierstrassCurve.toProjective, h3, h4, h6, hx, hy]
  constructor <;> ring

/-- Every normalized polynomial output chart preserves the two center coordinates. -/
theorem projectiveSpecialization_singular_origin (j k t : Fin 3)
    (f : AdditionOutputOpen W j k t →ₐ[R] S)
    (h3 : algebraMap R S W.a₃ = 0) (h4 : algebraMap R S W.a₄ = 0)
    (h6 : algebraMap R S W.a₆ = 0)
    (hx : f (additionOutputRestriction W j k t
      (chartProductRight W j k (coord W k 0))) = 0)
    (hy : f (additionOutputRestriction W j k t
      (chartProductRight W j k (coord W k 1))) = 0) :
    f (projectiveAdditionChart W j k t (coord W t 0)) = 0 ∧
      f (projectiveAdditionChart W j k t (coord W t 1)) = 0 := by
  let g := f.comp (additionOutputRestriction W j k t)
  have h := projectiveAdd_singular_origin (W.map (algebraMap R S))
    (g ∘ chartProductLeft W j k ∘ coord W j)
    (g ∘ chartProductRight W j k ∘ coord W k) h3 h4 h6 hx hy
  have he := chartProductAdditionCoordinates_map W j k g
  have hx' := (congrFun he 0).trans h.1
  have hy' := (congrFun he 1).trans h.2
  constructor
  · rw [projectiveAdditionChart_coord, map_mul]
    change f (additionOutputInverse W j k t) * g _ = 0
    rw [show g (chartProductAdditionCoordinates W j k 0) = 0 from hx', mul_zero]
  · rw [projectiveAdditionChart_coord, map_mul]
    change f (additionOutputInverse W j k t) * g _ = 0
    rw [show g (chartProductAdditionCoordinates W j k 1) = 0 from hy', mul_zero]

end FLT.Mazur.WeierstrassIntegralChart
