/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXMorphism
public import FLT.Mazur.WeierstrassDilatationCoefficients
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Coordinate maps on the overlap of the two modification charts

On the x-direction chart invert t; on the divided chart invert u. The actual
coordinate substitutions are (u,w) = (1/t,v/t) and (t,v) = (1/u,w/u).
The formulas work over arbitrary test algebras, without regularity hypotheses.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Inverting the incidence coordinate produces an actual divided-chart solution. -/
theorem divided_overlap_equation (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (t W s b3 b4 b6) = a) :
    let u := (↑a⁻¹ : S)
    let w := (↑a⁻¹ : S) * f (v W s b3 b4 b6)
    w ^ 2 + (algebraMap R S W.a₁ * u + algebraMap R S b3) * w =
      algebraMap R S s * u ^ 3 + algebraMap R S W.a₂ * u ^ 2 +
        algebraMap R S b4 * u + algebraMap R S b6 := by
  dsimp only
  have h := congrArg f (incidence W s b3 b4 b6)
  simp only [x, map_mul, map_add, map_sub, map_pow, AlgHom.commutes, ha] at h
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 3 * h -
    ((↑a⁻¹ : S) ^ 2 * (f (v W s b3 b4 b6) ^ 2 +
      algebraMap R S W.a₁ * f (v W s b3 b4 b6) - algebraMap R S W.a₂) +
      (1 + (↑a : S) * (↑a⁻¹ : S)) * (↑a⁻¹ : S) *
        (algebraMap R S b3 * f (v W s b3 b4 b6) - algebraMap R S b4) -
      (1 + (↑a : S) * (↑a⁻¹ : S) + ((↑a : S) * (↑a⁻¹ : S)) ^ 2) *
        algebraMap R S b6) * hi

/-- The divided chart maps to any x-chart algebra in which the overlap coordinate is a unit. -/
def dividedOverlapMap (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (t W s b3 b4 b6) = a) :
    WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S :=
  WeierstrassDilatation.evaluation W s b3 b4 b6 (↑a⁻¹ : S)
    ((↑a⁻¹ : S) * f (v W s b3 b4 b6))
    (divided_overlap_equation W s b3 b4 b6 f a ha)

/-- The divided horizontal coordinate is the inverse incidence coordinate. -/
@[simp] theorem dividedOverlapMap_x (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (t W s b3 b4 b6) = a) :
    dividedOverlapMap W s b3 b4 b6 f a ha (WeierstrassDilatation.x W s b3 b4 b6) =
      (↑a⁻¹ : S) := WeierstrassDilatation.evaluation_x _ _ _ _ _ _ _ _

/-- The divided vertical coordinate is the slope divided by the incidence coordinate. -/
@[simp] theorem dividedOverlapMap_y (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (t W s b3 b4 b6) = a) :
    dividedOverlapMap W s b3 b4 b6 f a ha (WeierstrassDilatation.y W s b3 b4 b6) =
      (↑a⁻¹ : S) * f (v W s b3 b4 b6) :=
  WeierstrassDilatation.evaluation_y _ _ _ _ _ _ _ _

/-- Conversely, inverting the divided horizontal coordinate solves the x-chart relation. -/
theorem x_overlap_equation (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.x W s b3 b4 b6) = a) :
    let t := (↑a⁻¹ : S)
    let v := (↑a⁻¹ : S) * f (WeierstrassDilatation.y W s b3 b4 b6)
    t * (v ^ 2 + (algebraMap R S W.a₁ + algebraMap R S b3 * t) * v -
      (algebraMap R S W.a₂ + algebraMap R S b4 * t + algebraMap R S b6 * t ^ 2)) =
        algebraMap R S s := by
  dsimp only
  have h := WeierstrassDilatation.equation_map W s b3 b4 b6 f
  rw [ha] at h
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 3 * h -
    (algebraMap R S W.a₁ * (↑a⁻¹ : S) ^ 2 *
        f (WeierstrassDilatation.y W s b3 b4 b6) -
      (1 + (↑a : S) * (↑a⁻¹ : S) + ((↑a : S) * (↑a⁻¹ : S)) ^ 2) * algebraMap R S s -
      (1 + (↑a : S) * (↑a⁻¹ : S)) * algebraMap R S W.a₂ * (↑a⁻¹ : S) -
      algebraMap R S b4 * (↑a⁻¹ : S) ^ 2) * hi

/-- The x-direction chart maps to any divided algebra on the complementary principal open. -/
def xOverlapMap (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.x W s b3 b4 b6) = a) :
    Coordinate W s b3 b4 b6 →ₐ[R] S :=
  evaluation W s b3 b4 b6 (↑a⁻¹ : S)
    ((↑a⁻¹ : S) * f (WeierstrassDilatation.y W s b3 b4 b6))
    (x_overlap_equation W s b3 b4 b6 f a ha)

/-- The incidence coordinate is the inverse divided horizontal coordinate. -/
@[simp] theorem xOverlapMap_t (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.x W s b3 b4 b6) = a) :
    xOverlapMap W s b3 b4 b6 f a ha (t W s b3 b4 b6) = (↑a⁻¹ : S) :=
  evaluation_t _ _ _ _ _ _ _ _

/-- The slope is the ratio of the divided coordinates. -/
@[simp] theorem xOverlapMap_v (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.x W s b3 b4 b6) = a) :
    xOverlapMap W s b3 b4 b6 f a ha (v W s b3 b4 b6) =
      (↑a⁻¹ : S) * f (WeierstrassDilatation.y W s b3 b4 b6) :=
  evaluation_v _ _ _ _ _ _ _ _

/-- Applying the opposite substitution returns every actual x-chart map on the overlap. -/
theorem xOverlapMap_dividedOverlapMap (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (t W s b3 b4 b6) = a) :
    xOverlapMap W s b3 b4 b6 (dividedOverlapMap W s b3 b4 b6 f a ha) a⁻¹
      (dividedOverlapMap_x W s b3 b4 b6 f a ha) = f := by
  apply hom_ext
  · simp only [xOverlapMap_t, inv_inv, ha]
  · simp only [xOverlapMap_v, inv_inv, dividedOverlapMap_y]
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-- The other composite returns every divided-chart map on the complementary overlap. -/
theorem dividedOverlapMap_xOverlapMap
    (f : WeierstrassDilatation.Coordinate W s b3 b4 b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.x W s b3 b4 b6) = a) :
    dividedOverlapMap W s b3 b4 b6 (xOverlapMap W s b3 b4 b6 f a ha) a⁻¹
      (xOverlapMap_t W s b3 b4 b6 f a ha) = f := by
  apply WeierstrassDilatation.hom_ext
  · simp only [dividedOverlapMap_x, inv_inv, ha]
  · simp only [dividedOverlapMap_y, inv_inv, xOverlapMap_v]
    rw [← mul_assoc, Units.mul_inv, one_mul]

end FLT.Mazur.WeierstrassModificationX
