/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXContraction

/-!
# The unchanged horizontal open of a successive modification

Away from the preceding horizontal coordinate, the inverse contraction has
explicit coordinates (π/x,y/x,x). These formulas recover every function in
both directions and will glue the unchanged part of the preceding chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BY" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)

/-- The old horizontal fractions solve the full successive chart equation. -/
theorem horizontal_equation (f : B →ₐ[R] S) (a : Sˣ) (ha : f BX = a) :
    ((↑a⁻¹ : S) * f BY) ^ 2 +
        (algebraMap R S W.a₁ + algebraMap R S b3 * (algebraMap R S π * (↑a⁻¹ : S))) *
          ((↑a⁻¹ : S) * f BY) =
      algebraMap R S s * (↑a : S) + algebraMap R S W.a₂ +
        algebraMap R S b4 * (algebraMap R S π * (↑a⁻¹ : S)) +
        algebraMap R S b6 * (algebraMap R S π * (↑a⁻¹ : S)) ^ 2 := by
  have he := WeierstrassDilatation.equation_map W s (π * b3) (π * b4) (π ^ 2 * b6) f
  simp only [ha, map_mul, map_pow] at he
  have hi : (↑a : S) * (↑a⁻¹ : S) = 1 := Units.mul_inv a
  linear_combination (↑a⁻¹ : S) ^ 2 * he +
    (-algebraMap R S W.a₁ * (↑a⁻¹ : S) * f BY +
      (algebraMap R S s * (↑a : S) + algebraMap R S W.a₂) *
        ((↑a : S) * (↑a⁻¹ : S) + 1) +
      algebraMap R S π * algebraMap R S b4 * (↑a⁻¹ : S)) * hi

/-- The inverse contraction wherever the preceding horizontal coordinate is a unit. -/
def horizontalMap (f : B →ₐ[R] S) (a : Sˣ) (ha : f BX = a) : A →ₐ[R] S :=
  evaluation W s π b3 b4 b6
    ![algebraMap R S π * (↑a⁻¹ : S), (↑a⁻¹ : S) * f BY, (↑a : S)]
    (horizontal_equation W s π b3 b4 b6 f a ha) (by
      change (algebraMap R S π * (↑a⁻¹ : S)) * (↑a : S) = algebraMap R S π
      rw [mul_assoc, Units.inv_mul, mul_one])

/-- Incidence is the old scale divided by the old horizontal coordinate. -/
@[simp] theorem horizontalMap_t (f : B →ₐ[R] S) (a : Sˣ) (ha : f BX = a) :
    horizontalMap W s π b3 b4 b6 f a ha (coord W s π b3 b4 b6 0) =
      algebraMap R S π * (↑a⁻¹ : S) := evaluation_coord _ _ _ _ _ _ _ _ _ _

/-- Slope is the ratio of the preceding divided coordinates. -/
@[simp] theorem horizontalMap_v (f : B →ₐ[R] S) (a : Sˣ) (ha : f BX = a) :
    horizontalMap W s π b3 b4 b6 f a ha (coord W s π b3 b4 b6 1) =
      (↑a⁻¹ : S) * f BY := evaluation_coord _ _ _ _ _ _ _ _ _ _

/-- The preceding horizontal coordinate is unchanged. -/
@[simp] theorem horizontalMap_u (f : B →ₐ[R] S) (a : Sˣ) (ha : f BX = a) :
    horizontalMap W s π b3 b4 b6 f a ha (coord W s π b3 b4 b6 2) = (↑a : S) :=
  evaluation_coord _ _ _ _ _ _ _ _ _ _

/-- Applying contraction after its horizontal inverse returns the preceding chart map. -/
theorem horizontalMap_fromDivided (f : B →ₐ[R] S) (a : Sˣ) (ha : f BX = a) :
    (horizontalMap W s π b3 b4 b6 f a ha).comp (fromDivided W s π b3 b4 b6) = f := by
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, fromDivided_x, horizontalMap_u, ha]
  · simp only [AlgHom.comp_apply, fromDivided_y, map_mul, horizontalMap_u, horizontalMap_v]
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-- Any map from the x-chart is recovered from its contraction on this horizontal open. -/
theorem horizontalMap_contraction (f : A →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s π b3 b4 b6 2) = a) :
    horizontalMap W s π b3 b4 b6 (f.comp (fromDivided W s π b3 b4 b6)) a
      (by simpa only [AlgHom.comp_apply, fromDivided_x] using ha) = f := by
  apply hom_ext
  intro i
  fin_cases i
  · change horizontalMap W s π b3 b4 b6 _ a _ (coord W s π b3 b4 b6 0) =
      f (coord W s π b3 b4 b6 0)
    rw [horizontalMap_t]
    have h := congrArg f (incidence W s π b3 b4 b6)
    simp only [map_mul, AlgHom.commutes, ha] at h
    rw [← h, mul_assoc, Units.mul_inv, mul_one]
  · change horizontalMap W s π b3 b4 b6 _ a _ (coord W s π b3 b4 b6 1) =
      f (coord W s π b3 b4 b6 1)
    rw [horizontalMap_v, AlgHom.comp_apply, fromDivided_y, map_mul, ha,
      ← mul_assoc, Units.inv_mul, one_mul]
  · change horizontalMap W s π b3 b4 b6 _ a _ (coord W s π b3 b4 b6 2) =
      f (coord W s π b3 b4 b6 2)
    rw [horizontalMap_u, ha]

end FLT.Mazur.WeierstrassSuccessiveX
