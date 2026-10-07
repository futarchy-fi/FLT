/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreAction
public import FLT.EllipticCurve.CubicLegendreFibers

/-! # Legendre fibers are orbits of the integral symmetry action

For points of the integral Legendre chart valued in any field, equality
of the actual curve j-invariant is equivalent to lying in the same orbit
of the six parameter symmetries. This includes characteristic three and
allows stabilizers at the special j-values.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
variable {K : Type*} [Field K] (p : ℕ) [NeZero p]
omit [NeZero p] in
/-- Evaluation of the swap on a field-valued parameter. -/
theorem legendreFieldParameter_swap (f : LegendreBase p →+* K) :
    (f.comp (legendreSwapParameterMap p)) (legendreParameter p) =
      1 - f (legendreParameter p) := by simp
omit [NeZero p] in
/-- Evaluation of the reciprocal on a field-valued parameter. -/
theorem legendreFieldParameter_reciprocal (f : LegendreBase p →+* K) :
    (f.comp (legendreReciprocalParameterMap p)) (legendreParameter p) =
      (f (legendreParameter p))⁻¹ := by
  rw [RingHom.comp_apply, legendreReciprocalParameterMap_parameter, map_units_inv,
    legendreParameterUnit_val]

/-- Each of the six parameter formulas is realized by the integral group action. -/
theorem legendreFieldParameter_orbit_of_six (f g : LegendreBase p →+* K)
    (h : g (legendreParameter p) = f (legendreParameter p) ∨
      g (legendreParameter p) = 1 - f (legendreParameter p) ∨
      g (legendreParameter p) = (f (legendreParameter p))⁻¹ ∨
      g (legendreParameter p) = (1 - f (legendreParameter p))⁻¹ ∨
      g (legendreParameter p) = f (legendreParameter p) / (f (legendreParameter p) - 1) ∨
      g (legendreParameter p) = (f (legendreParameter p) - 1) / f (legendreParameter p)) :
    ∃ a : DihedralGroup 3, g = f.comp (legendreParameterSymmetries p a).toRingHom := by
  have hs := legendreFieldParameter_swap (K := K) p
  have ht := legendreFieldParameter_reciprocal (K := K) p
  have hd : f (legendreParameter p) - 1 ≠ 0 := by
    simpa only [map_sub, map_one] using ((legendreBase_units p).2.2.2.map f).ne_zero
  have h1 : 1 - f (legendreParameter p) ≠ 0 :=
    sub_ne_zero.mpr (sub_ne_zero.mp hd).symm
  rcases h with h | h | h | h | h | h
  · refine ⟨.r 0, legendreRingHom_ext p _ _ ?_⟩
    change _ = f (legendreParameter p)
    exact h
  · refine ⟨.sr 0, legendreRingHom_ext p _ _ ?_⟩
    change _ = f (legendreSwapParameterMap p (legendreParameter p))
    simpa using h
  · refine ⟨.sr 1, legendreRingHom_ext p _ _ ?_⟩
    change _ = (f.comp (legendreReciprocalParameterMap p)) (legendreParameter p)
    rw [ht]
    exact h
  · refine ⟨.r 1, legendreRingHom_ext p _ _ ?_⟩
    change _ = ((f.comp (legendreSwapParameterMap p)).comp
      (legendreReciprocalParameterMap p)) (legendreParameter p)
    rw [ht, hs]
    exact h
  · refine ⟨.sr 2, legendreRingHom_ext p _ _ ?_⟩
    change _ = (((f.comp (legendreSwapParameterMap p)).comp
      (legendreReciprocalParameterMap p)).comp
      (legendreSwapParameterMap p)) (legendreParameter p)
    rw [hs, ht, hs, h]
    field_simp
    ring
  · refine ⟨.r 2, legendreRingHom_ext p _ _ ?_⟩
    change _ = ((f.comp (legendreReciprocalParameterMap p)).comp
      (legendreSwapParameterMap p)) (legendreParameter p)
    rw [hs, ht, h]
    have h0 := ((legendreBase_units p).2.2.1.map f).ne_zero
    field_simp

/-- Every element of the symmetry group fixes the actual universal j-invariant. -/
theorem legendreParameterSymmetries_j (a : DihedralGroup 3) :
    legendreParameterSymmetries p a (legendreModel p).j = (legendreModel p).j := by
  have h := (legendreParameterSymmetries p a).commutes Polynomial.X
  change legendreParameterSymmetries p a (legendreJMap p Polynomial.X) =
    legendreJMap p Polynomial.X at h
  simpa [legendreJMap] using h

/-- Two field-valued Legendre points have equal j exactly when they lie in the same orbit. -/
theorem legendreFieldPoint_orbit_iff_j (f g : LegendreBase p →+* K) :
    f (legendreModel p).j = g (legendreModel p).j ↔
      ∃ a : DihedralGroup 3, g = f.comp (legendreParameterSymmetries p a).toRingHom := by
  have hu (f : LegendreBase p →+* K) :
      IsUnit (2 : K) ∧ IsUnit (f (legendreParameter p)) ∧
        IsUnit (f (legendreParameter p) - 1) := by
    exact ⟨by simpa only [map_ofNat] using (legendreBase_units p).1.map f,
      (legendreBase_units p).2.2.1.map f,
      by simpa only [map_sub, map_one] using (legendreBase_units p).2.2.2.map f⟩
  have he (f : LegendreBase p →+* K) :
      (legendreCurve (f (legendreParameter p))).IsElliptic :=
    legendreCurve_elliptic _ (hu f).1 (hu f).2.1 (hu f).2.2
  have hj (f : LegendreBase p →+* K) :
      f (legendreModel p).j = (legendreCurve (f (legendreParameter p))).j := by
    simpa only [legendreModel, legendreCurve_map] using
      (WeierstrassCurve.map_j (legendreModel p) f).symm
  constructor
  · intro h
    apply legendreFieldParameter_orbit_of_six p f g
    apply (legendre_j_eq_iff_six _ _ (hu f).1.ne_zero
      (hu f).2.1.ne_zero (sub_ne_zero.mp (hu f).2.2.ne_zero)
      (hu g).2.1.ne_zero (sub_ne_zero.mp (hu g).2.2.ne_zero)).mp
    rw [← hj f, ← hj g]
    exact h
  · rintro ⟨a, rfl⟩
    rw [RingHom.comp_apply]
    change _ = f (legendreParameterSymmetries p a (legendreModel p).j)
    rw [legendreParameterSymmetries_j]

/-- The fixed coordinates and j identify exactly the same field-valued Legendre points. -/
theorem legendreFieldPoint_invariants_iff_j (f g : LegendreBase p →+* K) :
    f.comp (LegendreInvariantRing p).subtype = g.comp (LegendreInvariantRing p).subtype ↔
      f (legendreModel p).j = g (legendreModel p).j := by
  constructor
  · intro h
    let jinv : LegendreInvariantRing p :=
      ⟨(legendreModel p).j, fun a => legendreParameterSymmetries_j p a⟩
    exact DFunLike.congr_fun h jinv
  · intro h
    obtain ⟨a, rfl⟩ := (legendreFieldPoint_orbit_iff_j p f g).mp h
    ext x
    change f (x : LegendreBase p) =
      f (legendreParameterSymmetries p a (x : LegendreBase p))
    exact congrArg f (x.property a).symm


end WeierstrassCurve.CubicCharts
