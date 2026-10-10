/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYAlgebra
public import FLT.Mazur.WeierstrassModificationXAlgebra

/-!
# Maps from the y-direction principal opens

Where u=x/y is invertible, the x-direction coordinates are t=r/u and v=1/u.
Where r=s/y is invertible, the divided coordinates are x=u/r and y=1/r.
The equations are proved over arbitrary test algebras, including nonreduced ones.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Algebra maps preserve the actual divided cubic relation. -/
theorem equation_map (f : Coordinate W s b3 b4 b6 →ₐ[R] S) :
    1 + algebraMap R S W.a₁ * f (coord W s b3 b4 b6 1) +
        algebraMap R S b3 * f (coord W s b3 b4 b6 0) =
      f (coord W s b3 b4 b6 2) * f (coord W s b3 b4 b6 1) ^ 3 +
        algebraMap R S W.a₂ * f (coord W s b3 b4 b6 1) ^ 2 +
        algebraMap R S b4 * f (coord W s b3 b4 b6 0) * f (coord W s b3 b4 b6 1) +
        algebraMap R S b6 * f (coord W s b3 b4 b6 0) ^ 2 := by
  simpa only [map_add, map_mul, map_pow, map_one, AlgHom.commutes] using
    congrArg f (equation W s b3 b4 b6)

/-- Clearing the horizontal ratio recovers the actual original x-coordinate. -/
theorem x_overlap_recovery (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 1) = a) :
    let t := f (coord W s b3 b4 b6 0) * (↑a⁻¹ : S)
    (↑a⁻¹ : S) ^ 2 + (algebraMap R S W.a₁ + algebraMap R S b3 * t) * (↑a⁻¹ : S) -
      (algebraMap R S W.a₂ + algebraMap R S b4 * t + algebraMap R S b6 * t ^ 2) =
        f (coord W s b3 b4 b6 2) * (↑a : S) := by
  dsimp only
  have h := equation_map W s b3 b4 b6 f
  rw [ha] at h
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 2 * h +
    (-algebraMap R S W.a₁ * (↑a⁻¹ : S) +
      algebraMap R S W.a₂ * ((↑a : S) * (↑a⁻¹ : S) + 1) +
      algebraMap R S b4 * f (coord W s b3 b4 b6 0) * (↑a⁻¹ : S) +
      f (coord W s b3 b4 b6 2) * (↑a : S) * ((↑a : S) * (↑a⁻¹ : S) + 1)) * hi

/-- The actual x-direction map where the horizontal ratio is a unit. -/
def toX (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 1) = a) :
    WeierstrassModificationX.Coordinate W s b3 b4 b6 →ₐ[R] S :=
  WeierstrassModificationX.evaluation W s b3 b4 b6
    (f (coord W s b3 b4 b6 0) * (↑a⁻¹ : S)) (↑a⁻¹ : S) (by
      rw [x_overlap_recovery W s b3 b4 b6 f a ha]
      calc
        _ = f (coord W s b3 b4 b6 0) * f (coord W s b3 b4 b6 2) *
            ((↑a : S) * (↑a⁻¹ : S)) := by ring
        _ = algebraMap R S s := by
          rw [Units.mul_inv, mul_one, ← map_mul, incidence, AlgHom.commutes])

/-- The incidence coordinate on the x-overlap is r/u. -/
@[simp] theorem toX_t (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 1) = a) :
    toX W s b3 b4 b6 f a ha (WeierstrassModificationX.t W s b3 b4 b6) =
      f (coord W s b3 b4 b6 0) * (↑a⁻¹ : S) :=
  WeierstrassModificationX.evaluation_t _ _ _ _ _ _ _ _

/-- The slope coordinate on the x-overlap is 1/u. -/
@[simp] theorem toX_v (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 1) = a) :
    toX W s b3 b4 b6 f a ha (WeierstrassModificationX.v W s b3 b4 b6) =
      (↑a⁻¹ : S) := WeierstrassModificationX.evaluation_v _ _ _ _ _ _ _ _

/-- The x-direction map recovers the same original horizontal coordinate. -/
theorem toX_x (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 1) = a) :
    toX W s b3 b4 b6 f a ha (WeierstrassModificationX.x W s b3 b4 b6) =
      f (coord W s b3 b4 b6 2) * (↑a : S) := by
  simp only [WeierstrassModificationX.x, map_add, map_mul, map_sub, map_pow,
    AlgHom.commutes, toX_t, toX_v]
  exact x_overlap_recovery W s b3 b4 b6 f a ha

/-- Inverting the scale ratio solves the divided-chart equation. -/
theorem divided_overlap_equation (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 0) = a) :
    let u := f (coord W s b3 b4 b6 1) * (↑a⁻¹ : S)
    (↑a⁻¹ : S) ^ 2 + (algebraMap R S W.a₁ * u + algebraMap R S b3) * (↑a⁻¹ : S) =
      algebraMap R S s * u ^ 3 + algebraMap R S W.a₂ * u ^ 2 +
        algebraMap R S b4 * u + algebraMap R S b6 := by
  dsimp only
  have h := equation_map W s b3 b4 b6 f
  have hz := congrArg f (incidence W s b3 b4 b6)
  simp only [map_mul, AlgHom.commutes, ha] at hz
  rw [ha] at h
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 2 * h +
    f (coord W s b3 b4 b6 1) ^ 3 * (↑a⁻¹ : S) ^ 3 * hz +
    (-algebraMap R S b3 * (↑a⁻¹ : S) -
      f (coord W s b3 b4 b6 2) * f (coord W s b3 b4 b6 1) ^ 3 * (↑a⁻¹ : S) ^ 2 +
      algebraMap R S b4 * f (coord W s b3 b4 b6 1) * (↑a⁻¹ : S) +
      algebraMap R S b6 * ((↑a : S) * (↑a⁻¹ : S) + 1)) * hi

/-- The actual divided-chart map where the scale ratio is a unit. -/
def toDivided (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 0) = a) :
    WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S :=
  WeierstrassDilatation.evaluation W s b3 b4 b6
    (f (coord W s b3 b4 b6 1) * (↑a⁻¹ : S)) (↑a⁻¹ : S)
    (divided_overlap_equation W s b3 b4 b6 f a ha)

/-- The divided horizontal coordinate is u/r. -/
@[simp] theorem toDivided_x (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 0) = a) :
    toDivided W s b3 b4 b6 f a ha (WeierstrassDilatation.x W s b3 b4 b6) =
      f (coord W s b3 b4 b6 1) * (↑a⁻¹ : S) :=
  WeierstrassDilatation.evaluation_x _ _ _ _ _ _ _ _

/-- The divided vertical coordinate is 1/r. -/
@[simp] theorem toDivided_y (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (coord W s b3 b4 b6 0) = a) :
    toDivided W s b3 b4 b6 f a ha (WeierstrassDilatation.y W s b3 b4 b6) =
      (↑a⁻¹ : S) := WeierstrassDilatation.evaluation_y _ _ _ _ _ _ _ _

end FLT.Mazur.WeierstrassModificationY
