/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYOverlap
public import FLT.Mazur.WeierstrassDilatationCoefficients

/-!
# Reverse coordinate substitutions into the y-direction chart

Inverting the vertical divided coordinate or the x-direction slope supplies
actual y-chart evaluations. The proofs retain the original incidence relation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The inverse vertical divided coordinate solves the y-direction equation. -/
theorem fromDivided_equation (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.y W s b3 b4 b6) = a) :
    let u := f (WeierstrassDilatation.x W s b3 b4 b6)
    1 + algebraMap R S W.a₁ * (u * (↑a⁻¹ : S)) + algebraMap R S b3 * (↑a⁻¹ : S) =
      (algebraMap R S s * (↑a : S)) * (u * (↑a⁻¹ : S)) ^ 3 +
        algebraMap R S W.a₂ * (u * (↑a⁻¹ : S)) ^ 2 +
        algebraMap R S b4 * (↑a⁻¹ : S) * (u * (↑a⁻¹ : S)) +
        algebraMap R S b6 * (↑a⁻¹ : S) ^ 2 := by
  dsimp only
  have h := WeierstrassDilatation.equation_map W s b3 b4 b6 f
  rw [ha] at h
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 2 * h -
    (1 + (↑a : S) * (↑a⁻¹ : S) +
      algebraMap R S W.a₁ * f (WeierstrassDilatation.x W s b3 b4 b6) * (↑a⁻¹ : S) +
      algebraMap R S b3 * (↑a⁻¹ : S) +
      algebraMap R S s * f (WeierstrassDilatation.x W s b3 b4 b6) ^ 3 *
        (↑a⁻¹ : S) ^ 2) * hi

/-- The y-chart map on the open where the divided vertical coordinate is invertible. -/
def fromDivided (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.y W s b3 b4 b6) = a) :
    Coordinate W s b3 b4 b6 →ₐ[R] S :=
  evaluation W s b3 b4 b6
    ![(↑a⁻¹ : S), f (WeierstrassDilatation.x W s b3 b4 b6) * (↑a⁻¹ : S),
      algebraMap R S s * (↑a : S)]
    (fromDivided_equation W s b3 b4 b6 f a ha) (by
      change (↑a⁻¹ : S) * (algebraMap R S s * (↑a : S)) = _
      rw [mul_left_comm, Units.inv_mul, mul_one])

/-- The reverse map sends each universal coordinate to its explicit ratio. -/
@[simp] theorem fromDivided_coord
    (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.y W s b3 b4 b6) = a) (i : Fin 3) :
    fromDivided W s b3 b4 b6 f a ha (coord W s b3 b4 b6 i) =
      ![(↑a⁻¹ : S), f (WeierstrassDilatation.x W s b3 b4 b6) * (↑a⁻¹ : S),
        algebraMap R S s * (↑a : S)] i := evaluation_coord _ _ _ _ _ _ _ _ _

/-- The inverse x-direction slope solves the y-direction equation. -/
theorem fromX_equation (f : WeierstrassModificationX.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassModificationX.v W s b3 b4 b6) = a) :
    let t := f (WeierstrassModificationX.t W s b3 b4 b6)
    let x := f (WeierstrassModificationX.x W s b3 b4 b6)
    1 + algebraMap R S W.a₁ * (↑a⁻¹ : S) + algebraMap R S b3 * (t * (↑a⁻¹ : S)) =
      (x * (↑a : S)) * (↑a⁻¹ : S) ^ 3 + algebraMap R S W.a₂ * (↑a⁻¹ : S) ^ 2 +
        algebraMap R S b4 * (t * (↑a⁻¹ : S)) * (↑a⁻¹ : S) +
        algebraMap R S b6 * (t * (↑a⁻¹ : S)) ^ 2 := by
  dsimp only
  have hx : (↑a : S) ^ 2 + (algebraMap R S W.a₁ +
      algebraMap R S b3 * f (WeierstrassModificationX.t W s b3 b4 b6)) * (↑a : S) -
      (algebraMap R S W.a₂ + algebraMap R S b4 *
        f (WeierstrassModificationX.t W s b3 b4 b6) + algebraMap R S b6 *
        f (WeierstrassModificationX.t W s b3 b4 b6) ^ 2) =
      f (WeierstrassModificationX.x W s b3 b4 b6) := by
    simp only [WeierstrassModificationX.x, map_add, map_sub, map_mul, map_pow,
      AlgHom.commutes, ha]
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 2 * hx -
    (1 + (↑a : S) * (↑a⁻¹ : S) + (algebraMap R S W.a₁ +
      algebraMap R S b3 * f (WeierstrassModificationX.t W s b3 b4 b6)) * (↑a⁻¹ : S) +
      f (WeierstrassModificationX.x W s b3 b4 b6) * (↑a⁻¹ : S) ^ 2) * hi

/-- The y-chart map on the open where the x-direction slope is invertible. -/
def fromX (f : WeierstrassModificationX.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassModificationX.v W s b3 b4 b6) = a) :
    Coordinate W s b3 b4 b6 →ₐ[R] S :=
  evaluation W s b3 b4 b6
    ![f (WeierstrassModificationX.t W s b3 b4 b6) * (↑a⁻¹ : S), (↑a⁻¹ : S),
      f (WeierstrassModificationX.x W s b3 b4 b6) * (↑a : S)]
    (fromX_equation W s b3 b4 b6 f a ha) (by
      change (_ * (↑a⁻¹ : S)) * (_ * (↑a : S)) = _
      rw [mul_mul_mul_comm, Units.inv_mul, mul_one, ← map_mul,
        WeierstrassModificationX.incidence, AlgHom.commutes])

/-- The reverse x-direction map has the prescribed values on all three coordinates. -/
@[simp] theorem fromX_coord
    (f : WeierstrassModificationX.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassModificationX.v W s b3 b4 b6) = a) (i : Fin 3) :
    fromX W s b3 b4 b6 f a ha (coord W s b3 b4 b6 i) =
      ![f (WeierstrassModificationX.t W s b3 b4 b6) * (↑a⁻¹ : S), (↑a⁻¹ : S),
        f (WeierstrassModificationX.x W s b3 b4 b6) * (↑a : S)] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _

end FLT.Mazur.WeierstrassModificationY
