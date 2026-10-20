/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedVerticalSmooth
public import FLT.Mazur.RelativeJetSmoothObstruction

/-!
# The vertical tangent obstruction at a divided center

The scaled cubic still has a monic square in its ordinate. At a center where
both coordinates and the linear coefficients vanish, its vertical tangent
cannot lift to third-order jets, for any scale and quadratic coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open Polynomial PolygonNodePresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K]

/-- The quadratic ordinate gives an obstruction for every scaled cubic at its origin. -/
theorem dividedCenterJet_obstruction (a b s : K) (u v : Jet K 3)
    (hu : jetDrop u = 0) (hv : jetDrop v = jet 2 X) :
    v ^ 2 + algebraMap K _ a * u * v ≠
      algebraMap K _ s * u ^ 3 + algebraMap K _ b * u ^ 2 := by
  obtain ⟨p, rfl⟩ := jet_surjective 3 u
  obtain ⟨q, rfl⟩ := jet_surjective 3 v
  have hp := (jet_eq_iff 2 p 0).mp (by simpa only [jetDrop_jet, map_zero] using hu)
  have hq := (jet_eq_iff 2 q X).mp hv
  have hp0 : p.coeff 0 = 0 := by simpa using hp 0 (by omega)
  have hp1 : p.coeff 1 = 0 := by simpa using hp 1 (by omega)
  have hq0 : q.coeff 0 = 0 := by simpa using hq 0 (by omega)
  have hq1 : q.coeff 1 = 1 := by simpa using hq 1 (by omega)
  intro he
  have hC (z : K) : jet 3 (C z) = algebraMap K _ z := (jet 3).commutes z
  have hc := (jet_eq_iff 3 (q ^ 2 + C a * p * q) (C s * p ^ 3 + C b * p ^ 2)).mp
    (by simpa only [map_add, map_pow, map_mul, hC] using he)
  have hc2 := hc 2 (by omega)
  simp [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, hp0, hp1, hq0, hq1] at hc2

variable {R : Type*} [CommRing R] [Algebra R K]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : algebraMap R K b3 = 0) (h4 : algebraMap R K b4 = 0)
  (h6 : algebraMap R K b6 = 0)

/-- The vertical infinitesimal vector in the actual divided coordinate ring. -/
def dividedCenterTangent : Coordinate W s b3 b4 b6 →ₐ[R] Jet K 2 :=
  evaluation W s b3 b4 b6 0 (jet 2 X) (by
    have h3' : algebraMap R (Jet K 2) b3 = 0 := by
      rw [IsScalarTower.algebraMap_apply R K, h3, map_zero]
    have h6' : algebraMap R (Jet K 2) b6 = 0 := by
      rw [IsScalarTower.algebraMap_apply R K, h6, map_zero]
    simp only [mul_zero, h3', zero_mul, add_zero, h6',
      zero_pow (by omega : 3 ≠ 0), zero_pow (by omega : 2 ≠ 0)]
    rw [← map_pow, ← map_zero (jet 2), jet_eq_iff]
    intro d hd
    simp [coeff_X_pow, show d ≠ 2 by omega])

/-- The tangent fixes the abscissa at the center. -/
@[simp] theorem dividedCenterTangent_x :
    dividedCenterTangent W s b3 b4 b6 h3 h6 (x W s b3 b4 b6) = 0 :=
  evaluation_x _ _ _ _ _ _ _ _

/-- The ordinate is the nonzero first-order infinitesimal direction. -/
@[simp] theorem dividedCenterTangent_y :
    dividedCenterTangent W s b3 b4 b6 h3 h6 (y W s b3 b4 b6) = jet 2 X :=
  evaluation_y _ _ _ _ _ _ _ _

include h4 in
/-- No third-order lift satisfies the original divided equation at this center. -/
theorem dividedCenterTangent_no_lift
    (g : Coordinate W s b3 b4 b6 →ₐ[R] Jet K 3) :
    ((jetDrop (K := K)).restrictScalars R).comp g ≠
      dividedCenterTangent W s b3 b4 b6 h3 h6 := by
  intro h
  have hx : jetDrop (g (x W s b3 b4 b6)) = 0 := by
    simpa using AlgHom.congr_fun h (x W s b3 b4 b6)
  have hy : jetDrop (g (y W s b3 b4 b6)) = jet 2 X := by
    simpa using AlgHom.congr_fun h (y W s b3 b4 b6)
  apply dividedCenterJet_obstruction (algebraMap R K W.a₁)
    (algebraMap R K W.a₂) (algebraMap R K s) _ _ hx hy
  simpa only [IsScalarTower.algebraMap_apply R K (Jet K 3), h3, h4, h6,
    map_zero, add_zero, zero_mul] using equation_map W s b3 b4 b6 g

end FLT.Mazur.WeierstrassDilatation
