/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationMorphism
public import FLT.Mazur.WeierstrassAdditionCenterContainment
public import FLT.Mazur.RegularCenterQuotientLinear

/-!
# Original center quotients are the actual divided coordinates

A divided algebra point makes the original center principal. Regularity of
the original scale then identifies both center quotients with its coordinates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassIntegralChart RegularCenter
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (g : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S) (φ : S →ₐ[R] B)
  (L : Coordinate W s b3 b4 b6 →ₐ[R] B)
  (hL : L.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) = φ.comp g)
local notation "I" => Ideal.map g.toRingHom (modificationChartCenter W s 2)
local notation "z" => algebraMap R B s

include hL in
/-- A genuine divided point principalizes the full original three-generator center. -/
theorem originalDividedPoint_center : (I).map φ.toRingHom = Ideal.span {z} := by
  rw [modificationChartCenter_map, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes]
  have hx := congrArg (fun f => f (coord W 2 0)) hL
  have hy := congrArg (fun f => f (coord W 2 1)) hL
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y,
    map_mul, AlgHom.commutes] at hx hy
  rw [← hx, ← hy]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact Ideal.subset_span rfl
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · exact Ideal.span_mono (by intro q hq; simp only [Set.mem_singleton_iff] at hq; simp [hq])

variable (J : Ideal S) (hz : IsRegular (algebraMap R B s))
  (hI : J.map φ.toRingHom = Ideal.span {algebraMap R B s})

include hL hz hI in
/-- Division of the original horizontal coordinate gives exactly the divided horizontal point. -/
theorem originalDividedPoint_quotient_x (hx : g (coord W 2 0) ∈ J) :
    quotient J φ.toRingHom z hI (g (coord W 2 0)) hx = L (x W s b3 b4 b6) := by
  symm
  apply quotient_unique J φ.toRingHom z hI hz
  have h := congrArg (fun f => f (coord W 2 0)) hL
  simp only [AlgHom.comp_apply, fromOriginal_x, map_mul, AlgHom.commutes] at h
  exact h

include hL hz hI in
/-- Division of the original vertical coordinate gives exactly the divided vertical point. -/
theorem originalDividedPoint_quotient_y (hy : g (coord W 2 1) ∈ J) :
    quotient J φ.toRingHom z hI (g (coord W 2 1)) hy = L (y W s b3 b4 b6) := by
  symm
  apply quotient_unique J φ.toRingHom z hI hz
  have h := congrArg (fun f => f (coord W 2 1)) hL
  simp only [AlgHom.comp_apply, fromOriginal_y, map_mul, AlgHom.commutes] at h
  exact h

end FLT.Mazur.WeierstrassDilatation
