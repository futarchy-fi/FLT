/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYReverse

/-!
# Inverse laws for the y-direction coordinate substitutions

The ratio substitutions are inverse on arbitrary test algebras where the
appropriate coordinate is a unit. In particular, the original vertical
coordinate is recovered using the actual incidence relation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Going through the divided chart preserves every original y-chart coordinate. -/
theorem fromDivided_toDivided (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 0) = a) :
    fromDivided W s b3 b4 b6 (toDivided W s b3 b4 b6 f a ha) a⁻¹
      (toDivided_y W s b3 b4 b6 f a ha) = f := by
  apply hom_ext
  intro i
  fin_cases i
  · simp [ha]
  · simp only [fromDivided_coord, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      inv_inv, toDivided_x]
    rw [mul_assoc, Units.inv_mul, mul_one]
  · rw [fromDivided_coord]
    change algebraMap R S s * (↑a⁻¹ : S) = f (coord W s b3 b4 b6 2)
    have h := congrArg f (incidence W s b3 b4 b6)
    simp only [map_mul, AlgHom.commutes, ha] at h
    rw [← h, mul_right_comm, Units.mul_inv, one_mul]

/-- Going through the y-chart preserves both divided coordinates. -/
theorem toDivided_fromDivided
    (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.y W s b3 b4 b6) = a) :
    toDivided W s b3 b4 b6 (fromDivided W s b3 b4 b6 f a ha) a⁻¹
      (fromDivided_coord W s b3 b4 b6 f a ha 0) = f := by
  apply WeierstrassDilatation.hom_ext
  · simp only [toDivided_x, fromDivided_coord, Matrix.cons_val_one, Matrix.cons_val_zero,
      inv_inv]
    rw [mul_assoc, Units.inv_mul, mul_one]
  · simp only [toDivided_y, inv_inv, ha]

/-- Going through the x-direction chart preserves all y-direction coordinates. -/
theorem fromX_toX (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 1) = a) :
    fromX W s b3 b4 b6 (toX W s b3 b4 b6 f a ha) a⁻¹
      (toX_v W s b3 b4 b6 f a ha) = f := by
  apply hom_ext
  intro i
  fin_cases i
  · simp only [fromX_coord, Fin.zero_eta, Matrix.cons_val_zero, toX_t, inv_inv]
    rw [mul_assoc, Units.inv_mul, mul_one]
  · simp [ha]
  · rw [fromX_coord]
    change toX W s b3 b4 b6 f a ha (WeierstrassModificationX.x W s b3 b4 b6) *
      (↑a⁻¹ : S) = f (coord W s b3 b4 b6 2)
    rw [toX_x]
    rw [mul_assoc, Units.mul_inv, mul_one]

/-- Going through the y-chart preserves both x-direction coordinates. -/
theorem toX_fromX (f : WeierstrassModificationX.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassModificationX.v W s b3 b4 b6) = a) :
    toX W s b3 b4 b6 (fromX W s b3 b4 b6 f a ha) a⁻¹
      (fromX_coord W s b3 b4 b6 f a ha 1) = f := by
  apply WeierstrassModificationX.hom_ext
  · simp only [toX_t, fromX_coord, Matrix.cons_val_zero, inv_inv]
    rw [mul_assoc, Units.inv_mul, mul_one]
  · simp only [toX_v, inv_inv, ha]

end FLT.Mazur.WeierstrassModificationY
