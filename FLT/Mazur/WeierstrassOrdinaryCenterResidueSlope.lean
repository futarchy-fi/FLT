/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionCenterContainment

/-!
# Residue slopes on regular principalizations of the original center

A residue map killing the principal center kills the original input coordinates.
The secant relation then identifies both character coefficients from the smooth input.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S B C : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing B] [CommRing C] (W : WeierstrassCurve R) (s : R) (b : Bool)
  (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
local notation "I" => Ideal.map
  (AlgHom.toRingHom (AlgHom.comp f (ordinaryInputRight W b)))
  (modificationChartCenter W s 2)
variable (φ : S →+* B) (z : B) (hI : ((modificationChartCenter W s 2).map
    (f.comp (ordinaryInputRight W b)).toRingHom).map φ = Ideal.span {z})
  (ψ : B →+* C) (hψ : ψ z = 0)
local notation "e" => RingHom.comp ψ φ

include hI hψ in
/-- Original node coordinates vanish on the residue of any principalized center. -/
theorem ordinaryCenterResidue_right_zero :
    e (f (ordinaryInputRight W b (coord W 2 0))) = 0 ∧
      e (f (ordinaryInputRight W b (coord W 2 1))) = 0 := by
  have hle : (I).map φ ≤ RingHom.ker ψ := by
    rw [hI, Ideal.span_singleton_le_iff_mem]
    exact hψ
  have hkill (t : S) (ht : t ∈ I) : e t = 0 :=
    hle (Ideal.mem_map_of_mem φ ht)
  constructor <;> apply hkill <;> rw [modificationChartCenter_map] <;>
    exact Ideal.subset_span (by simp)

variable (r q : Cˣ)
  (hx : (ψ.comp φ) (f (ordinaryInputLeft W b (coord W 2 0))) = (r : C) * q)
  (hy : (ψ.comp φ) (f (ordinaryInputLeft W b (coord W 2 1))) = (r : C) ^ 2 * q)

include hI hψ hx hy in
/-- The genuine integral chart slope restricts to the smooth input's normalized slope. -/
theorem ordinaryCenterResidue_slope : e (f (ordinaryChartSlope W b)) = r := by
  obtain ⟨h0, h1⟩ := ordinaryCenterResidue_right_zero W s b f φ z hI ψ hψ
  have h := congrArg e (ordinarySpecialization_line W b f)
  simp only [map_mul, map_sub, hx, hy, h0, h1, sub_zero] at h
  apply (r * q).isUnit.mul_left_inj.mp
  change _ * ((r : C) * q) = (r : C) * ((r : C) * q)
  linear_combination h

include hI hψ hx hy in
/-- The opposite coefficient is the other actual smooth-input unit. -/
theorem ordinaryCenterResidue_opposite_slope
    (hq : (q : C) = (r : C) + e (algebraMap R S W.a₁)) :
    e (f (ordinaryChartSlope W b) + algebraMap R S W.a₁) = q := by
  rw [map_add, ordinaryCenterResidue_slope W s b f φ z hI ψ hψ r q hx hy, hq]

end FLT.Mazur.WeierstrassIntegralChart
