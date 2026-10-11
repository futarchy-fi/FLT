/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra
public import FLT.Mazur.WeierstrassModificationXAlgebra

/-!
# Comparing successive charts with the modification at the product scale

The original incidence and slope give a map from the modification at scale
s*pi into the successive chart. Where incidence is invertible the inverse
recovers the successive horizontal coordinate as pi divided by incidence.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" => WeierstrassModificationX.Coordinate W (s * π) b3 b4 b6
local notation "t" => coord W s π b3 b4 b6 0
local notation "v" => coord W s π b3 b4 b6 1
local notation "u" => coord W s π b3 b4 b6 2
local notation "t'" => WeierstrassModificationX.t W (s * π) b3 b4 b6
local notation "v'" => WeierstrassModificationX.v W (s * π) b3 b4 b6
local notation "x'" => WeierstrassModificationX.x W (s * π) b3 b4 b6

/-- The successive equation expresses the original horizontal function with its scale. -/
theorem modification_horizontal :
    v ^ 2 + (algebraMap R A W.a₁ + algebraMap R A b3 * t) * v -
      (algebraMap R A W.a₂ + algebraMap R A b4 * t + algebraMap R A b6 * t ^ 2) =
        algebraMap R A s * u := by
  linear_combination equation W s π b3 b4 b6

/-- The actual product-scale modification functions in the successive chart. -/
def modificationMap : B →ₐ[R] A :=
  WeierstrassModificationX.evaluation W (s * π) b3 b4 b6 t v (by
    rw [modification_horizontal, map_mul, mul_left_comm, incidence])

/-- The original incidence ratio is unchanged. -/
@[simp] theorem modificationMap_t : modificationMap W s π b3 b4 b6 t' = t :=
  WeierstrassModificationX.evaluation_t _ _ _ _ _ _ _ _

/-- The original slope is unchanged. -/
@[simp] theorem modificationMap_v : modificationMap W s π b3 b4 b6 v' = v :=
  WeierstrassModificationX.evaluation_v _ _ _ _ _ _ _ _

/-- The original horizontal function retains its preceding scale factor. -/
@[simp] theorem modificationMap_x :
    modificationMap W s π b3 b4 b6 x' = algebraMap R A s * u := by
  simp only [WeierstrassModificationX.x, map_sub, map_add, map_mul, map_pow, AlgHom.commutes,
    modificationMap_v, modificationMap_t]
  exact modification_horizontal W s π b3 b4 b6

/-- The recovered horizontal coordinate satisfies the full successive equation. -/
theorem modificationIncidence_equation (f : B →ₐ[R] S) (z : Sˣ) (hz : f t' = z) :
    f v' ^ 2 + (algebraMap R S W.a₁ + algebraMap R S b3 * f t') * f v' =
      algebraMap R S s * (algebraMap R S π * (↑z⁻¹ : S)) + algebraMap R S W.a₂ +
        algebraMap R S b4 * f t' + algebraMap R S b6 * f t' ^ 2 := by
  have h := congrArg f (WeierstrassModificationX.incidence W (s * π) b3 b4 b6)
  simp only [map_mul, AlgHom.commutes, hz] at h
  have hx : f x' = algebraMap R S s * (algebraMap R S π * (↑z⁻¹ : S)) := by
    calc
      f x' = (↑z⁻¹ : S) * ((↑z : S) * f x') := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [h]; ring
  simp only [WeierstrassModificationX.x, map_sub, map_add, map_mul, map_pow,
    AlgHom.commutes] at hx
  linear_combination hx

/-- The inverse chart map wherever the original incidence function is a unit. -/
def modificationIncidenceInverse (f : B →ₐ[R] S) (z : Sˣ) (hz : f t' = z) : A →ₐ[R] S :=
  evaluation W s π b3 b4 b6 ![f t', f v', algebraMap R S π * (↑z⁻¹ : S)]
    (modificationIncidence_equation W s π b3 b4 b6 f z hz) (by
      change f t' * (algebraMap R S π * (↑z⁻¹ : S)) = algebraMap R S π
      rw [hz, mul_left_comm, Units.mul_inv, mul_one])

/-- The inverse keeps both original coordinates and recovers the horizontal coordinate. -/
@[simp] theorem modificationIncidenceInverse_coord
    (f : B →ₐ[R] S) (z : Sˣ) (hz : f t' = z) (i : Fin 3) :
    modificationIncidenceInverse W s π b3 b4 b6 f z hz (coord W s π b3 b4 b6 i) =
      ![f t', f v', algebraMap R S π * (↑z⁻¹ : S)] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- Inverse incidence transport preserves every original modification function. -/
theorem modificationIncidenceInverse_comp
    (f : B →ₐ[R] S) (z : Sˣ) (hz : f t' = z) :
    (modificationIncidenceInverse W s π b3 b4 b6 f z hz).comp
      (modificationMap W s π b3 b4 b6) = f := by
  apply WeierstrassModificationX.hom_ext <;>
    simp only [AlgHom.comp_apply, modificationMap_t, modificationMap_v,
      modificationIncidenceInverse_coord, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every successive map with invertible incidence is recovered from its original functions. -/
theorem modificationIncidenceInverse_recover
    (f : A →ₐ[R] S) (z : Sˣ) (hz : f t = z) :
    modificationIncidenceInverse W s π b3 b4 b6
      (f.comp (modificationMap W s π b3 b4 b6)) z
      (by simpa only [AlgHom.comp_apply, modificationMap_t] using hz) = f := by
  apply hom_ext
  intro i
  fin_cases i
  · change modificationIncidenceInverse W s π b3 b4 b6 _ z _ t = f t
    simp only [modificationIncidenceInverse_coord, Matrix.cons_val_zero,
      AlgHom.comp_apply, modificationMap_t]
  · change modificationIncidenceInverse W s π b3 b4 b6 _ z _ v = f v
    rw [modificationIncidenceInverse_coord]
    change f (modificationMap W s π b3 b4 b6 v') = f v
    rw [modificationMap_v]
  · change modificationIncidenceInverse W s π b3 b4 b6 _ z _ u = f u
    rw [modificationIncidenceInverse_coord]
    change algebraMap R S π * (↑z⁻¹ : S) = f u
    have h := congrArg f (incidence W s π b3 b4 b6)
    simp only [map_mul, AlgHom.commutes, hz] at h
    rw [← h, mul_right_comm, Units.mul_inv, one_mul]

end FLT.Mazur.WeierstrassSuccessiveX
