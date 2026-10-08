/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalChart
public import FLT.Mazur.NodeSmoothLocus

/-!
# The singular origin of the actual split nodal Weierstrass chart

The vertical tangent vector of Y²+aXY=X³ cannot lift from second to third
order. Thus the original Z chart is not formally smooth at its origin.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial PolygonNodePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (a : Kˣ)

/-- The vertical tangent obstruction allows any mixed-term coefficient. -/
theorem splitNodalJet_obstruction (c : K) (x y : Jet K 3)
    (hx : jetDrop x = 0) (hy : jetDrop y = jet 2 X) :
    y ^ 2 + algebraMap K _ c * x * y - x ^ 3 ≠ 0 := by
  obtain ⟨p, rfl⟩ := jet_surjective 3 x
  obtain ⟨q, rfl⟩ := jet_surjective 3 y
  have hp := (jet_eq_iff 2 p 0).mp (by simpa only [jetDrop_jet, map_zero] using hx)
  have hq := (jet_eq_iff 2 q X).mp hy
  have hp0 : p.coeff 0 = 0 := by simpa using hp 0 (by omega)
  have hp1 : p.coeff 1 = 0 := by simpa using hp 1 (by omega)
  have hq0 : q.coeff 0 = 0 := by simpa using hq 0 (by omega)
  have hq1 : q.coeff 1 = 1 := by simpa using hq 1 (by omega)
  intro h
  have hc := (jet_eq_iff 3 (q ^ 2 + C c * p * q - p ^ 3) 0).mp (by
    have hC : jet (K := K) 3 (C c) = algebraMap K _ c := (jet 3).commutes c
    simpa only [map_sub, map_add, map_pow, map_mul, hC, map_zero] using h)
  have := hc 2 (by omega)
  simp [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, hp0, hp1, hq0, hq1] at this

/-- The relation in the original finite chart of the nodal cubic. -/
theorem splitNodalAffine_relation :
    coord (splitNodalEquation a) 2 1 ^ 2 +
      algebraMap K _ a * coord (splitNodalEquation a) 2 0 *
        coord (splitNodalEquation a) 2 1 - coord (splitNodalEquation a) 2 0 ^ 3 = 0 := by
  have h := coord_equation (splitNodalEquation a) 2
  rw [WeierstrassCurve.Projective.equation_iff] at h
  dsimp [splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective] at h ⊢
  simpa only [coord_self, map_zero, zero_mul, add_zero, mul_one, one_pow] using h

/-- Evaluation at the singular origin in the original affine chart. -/
def splitNodalOriginEval : Coordinate (splitNodalEquation a) 2 →ₐ[K] K :=
  evaluation _ 2 ![0, 0, 1] (by
    rw [WeierstrassCurve.Projective.equation_iff]
    simp [splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective]) rfl

@[simp] theorem splitNodalOriginEval_coord (i : Fin 3) :
    splitNodalOriginEval a (coord (splitNodalEquation a) 2 i) = ![0, 0, 1] i :=
  evaluation_coord _ _ _ _ _ i

/-- The vertical tangent vector in the original finite chart. -/
def splitNodalTangent : Coordinate (splitNodalEquation a) 2 →ₐ[K] Jet K 2 :=
  evaluation _ 2 ![0, jet 2 X, 1] (by
    rw [WeierstrassCurve.Projective.equation_iff]
    change jet (K := K) 2 X ^ 2 * 1 + algebraMap K _ a * 0 * jet 2 X * 1 +
      algebraMap K _ 0 * jet 2 X * 1 ^ 2 -
      (0 ^ 3 + algebraMap K _ 0 * 0 ^ 2 * 1 +
        algebraMap K _ 0 * 0 * 1 ^ 2 + algebraMap K _ 0 * 1 ^ 3) = 0
    simp only [map_zero, mul_zero, zero_mul, zero_pow (by omega : 3 ≠ 0),
      add_zero, mul_one, sub_zero]
    rw [← map_pow, ← map_zero (jet 2), jet_eq_iff]
    intro d hd
    simp [coeff_X_pow, show d ≠ 2 by omega]) rfl

@[simp] theorem splitNodalTangent_coord (i : Fin 3) :
    splitNodalTangent a (coord (splitNodalEquation a) 2 i) = ![0, jet 2 X, 1] i :=
  evaluation_coord _ _ _ _ _ i

/-- No lift of the vertical tangent vector respects the actual cubic relation. -/
theorem splitNodalTangent_no_lift
    (g : Coordinate (splitNodalEquation a) 2 →ₐ[K] Jet K 3) :
    jetDrop.comp g ≠ splitNodalTangent a := by
  intro h
  have hx : jetDrop (g (coord (splitNodalEquation a) 2 0)) = 0 := by
    simpa using AlgHom.congr_fun h (coord (splitNodalEquation a) 2 0)
  have hy : jetDrop (g (coord (splitNodalEquation a) 2 1)) = jet 2 X := by
    simpa using AlgHom.congr_fun h (coord (splitNodalEquation a) 2 1)
  apply splitNodalJet_obstruction (a : K) _ _ hx hy
  simpa only [map_sub, map_add, map_pow, map_mul, AlgHom.commutes, map_zero] using
    congrArg g (splitNodalAffine_relation a)

/-- The local ring at the actual affine origin is not formally smooth over the field. -/
theorem splitNodalOrigin_not_formallySmooth : ¬ Algebra.FormallySmooth K
    (Localization.AtPrime (RingHom.ker (splitNodalOriginEval a).toRingHom)) := by
  refine origin_not_formallySmooth (splitNodalOriginEval a) (splitNodalTangent a) ?_
    (splitNodalTangent_no_lift a)
  apply hom_ext
  intro i
  fin_cases i <;> simp [AlgHom.comp_apply]

end FLT.Mazur.WeierstrassIntegralChart
