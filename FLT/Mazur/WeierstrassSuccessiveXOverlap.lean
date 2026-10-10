/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXContraction

/-!
# Coordinate substitutions on successive modification overlaps

Inverting t gives the next divided coordinates (1/t,v/t). Conversely,
inverting the next divided horizontal coordinate gives (t,v,u) = (1/x,y/x,π*x).
Both maps are constructed from the actual equations over any test algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "D" => WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6
local notation "DX" => WeierstrassDilatation.x W (s * π) b3 b4 b6
local notation "DY" => WeierstrassDilatation.y W (s * π) b3 b4 b6

/-- Inverting incidence solves the next divided equation, with cubic coefficient s*π. -/
theorem divided_overlap_equation (f : A →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s π b3 b4 b6 0) = a) :
    let q := (↑a⁻¹ : S)
    let v := f (coord W s π b3 b4 b6 1)
    (q * v) ^ 2 + (algebraMap R S W.a₁ * q + algebraMap R S b3) * (q * v) =
      algebraMap R S (s * π) * q ^ 3 + algebraMap R S W.a₂ * q ^ 2 +
        algebraMap R S b4 * q + algebraMap R S b6 := by
  dsimp only
  have he := congrArg f (equation W s π b3 b4 b6)
  have ht := congrArg f (incidence W s π b3 b4 b6)
  simp only [map_mul, map_add, map_pow, AlgHom.commutes, ha] at he ht
  rw [map_mul]
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 2 * he +
    algebraMap R S s * (↑a⁻¹ : S) ^ 3 * ht -
    (algebraMap R S b3 * (↑a⁻¹ : S) * f (coord W s π b3 b4 b6 1) -
      algebraMap R S b4 * (↑a⁻¹ : S) +
      algebraMap R S s * (↑a⁻¹ : S) ^ 2 * f (coord W s π b3 b4 b6 2) -
      algebraMap R S b6 * ((↑a : S) * (↑a⁻¹ : S) + 1)) * hi

/-- The actual next divided chart maps into every incidence-invertible test algebra. -/
def dividedOverlapMap (f : A →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s π b3 b4 b6 0) = a) : D →ₐ[R] S :=
  WeierstrassDilatation.evaluation W (s * π) b3 b4 b6 (↑a⁻¹ : S)
    ((↑a⁻¹ : S) * f (coord W s π b3 b4 b6 1))
    (divided_overlap_equation W s π b3 b4 b6 f a ha)

/-- The new divided horizontal coordinate is the inverse incidence coordinate. -/
@[simp] theorem dividedOverlapMap_x (f : A →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s π b3 b4 b6 0) = a) :
    dividedOverlapMap W s π b3 b4 b6 f a ha DX = (↑a⁻¹ : S) :=
  WeierstrassDilatation.evaluation_x _ _ _ _ _ _ _ _

/-- The new divided vertical coordinate is slope divided by incidence. -/
@[simp] theorem dividedOverlapMap_y (f : A →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s π b3 b4 b6 0) = a) :
    dividedOverlapMap W s π b3 b4 b6 f a ha DY =
      (↑a⁻¹ : S) * f (coord W s π b3 b4 b6 1) :=
  WeierstrassDilatation.evaluation_y _ _ _ _ _ _ _ _

/-- The inverse substitution solves the full successive x-direction equation. -/
theorem x_overlap_equation (f : D →ₐ[R] S) (a : Sˣ) (ha : f DX = a) :
    ((↑a⁻¹ : S) * f DY) ^ 2 +
        (algebraMap R S W.a₁ + algebraMap R S b3 * (↑a⁻¹ : S)) *
          ((↑a⁻¹ : S) * f DY) =
      algebraMap R S s * (algebraMap R S π * (↑a : S)) + algebraMap R S W.a₂ +
        algebraMap R S b4 * (↑a⁻¹ : S) + algebraMap R S b6 * (↑a⁻¹ : S) ^ 2 := by
  have he := WeierstrassDilatation.equation_map W (s * π) b3 b4 b6 f
  rw [ha, map_mul] at he
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 2 * he +
    (-algebraMap R S W.a₁ * (↑a⁻¹ : S) * f DY +
      (algebraMap R S s * algebraMap R S π * (↑a : S) + algebraMap R S W.a₂) *
        ((↑a : S) * (↑a⁻¹ : S) + 1) + algebraMap R S b4 * (↑a⁻¹ : S)) * hi

/-- The actual successive x-direction map on the new divided principal open. -/
def xOverlapMap (f : D →ₐ[R] S) (a : Sˣ) (ha : f DX = a) : A →ₐ[R] S :=
  evaluation W s π b3 b4 b6
    ![(↑a⁻¹ : S), (↑a⁻¹ : S) * f DY, algebraMap R S π * (↑a : S)]
    (x_overlap_equation W s π b3 b4 b6 f a ha) (by
      change (↑a⁻¹ : S) * (algebraMap R S π * (↑a : S)) = algebraMap R S π
      rw [mul_left_comm, Units.inv_mul, mul_one])

/-- The reverse map sends incidence to the inverse new horizontal coordinate. -/
@[simp] theorem xOverlapMap_t (f : D →ₐ[R] S) (a : Sˣ) (ha : f DX = a) :
    xOverlapMap W s π b3 b4 b6 f a ha (coord W s π b3 b4 b6 0) = (↑a⁻¹ : S) :=
  evaluation_coord _ _ _ _ _ _ _ _ _ _

/-- The reverse map sends slope to the ratio of the new divided coordinates. -/
@[simp] theorem xOverlapMap_v (f : D →ₐ[R] S) (a : Sˣ) (ha : f DX = a) :
    xOverlapMap W s π b3 b4 b6 f a ha (coord W s π b3 b4 b6 1) =
      (↑a⁻¹ : S) * f DY := evaluation_coord _ _ _ _ _ _ _ _ _ _

/-- The retained old horizontal coordinate is π times the new one. -/
@[simp] theorem xOverlapMap_u (f : D →ₐ[R] S) (a : Sˣ) (ha : f DX = a) :
    xOverlapMap W s π b3 b4 b6 f a ha (coord W s π b3 b4 b6 2) =
      algebraMap R S π * (↑a : S) := evaluation_coord _ _ _ _ _ _ _ _ _ _

end FLT.Mazur.WeierstrassSuccessiveX
