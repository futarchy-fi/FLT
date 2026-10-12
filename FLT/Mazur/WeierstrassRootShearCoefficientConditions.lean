/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRootShearSmoothParameter

/-!
# Root and tangent hypotheses under actual coefficient change

Mapping the chosen root and tangent unit proves every equation needed by the
specialized smooth parametrization, over arbitrary coefficient algebras.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (W : WeierstrassCurve R) (f : S →ₐ[R] T)
  (r : S) (a : Sˣ)
  (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0)
  (h6 : (W.map (algebraMap R S)).a₆ = 0)

include ha in
/-- The actual mapped tangent unit has the specialized root's tangent coefficient. -/
theorem rootShearCoefficient_tangent :
    ((Units.map f.toRingHom a : Tˣ) : T) = (W.map (algebraMap R T)).a₁ + 2 * f r := by
  change f (a : S) = algebraMap R T W.a₁ + 2 * f r
  rw [ha]
  change f (algebraMap R S W.a₁ + 2 * r) = _
  rw [map_add, map_mul, map_ofNat, f.commutes]

include hr in
/-- The actual mapped root satisfies the specialized original tangent equation. -/
theorem rootShearCoefficient_root :
    (f r) ^ 2 + (W.map (algebraMap R T)).a₁ * f r - (W.map (algebraMap R T)).a₂ = 0 := by
  have H := congrArg f hr
  change f (r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂) = f 0 at H
  change f r ^ 2 + algebraMap R T W.a₁ * f r - algebraMap R T W.a₂ = 0
  simpa only [map_sub, map_add, map_pow, map_mul, f.commutes, map_zero] using H

include f h3 h4 h6 in
/-- All three vanishing original coefficients specialize without any reducedness condition. -/
theorem rootShearCoefficient_vanishing :
    (W.map (algebraMap R T)).a₃ = 0 ∧ (W.map (algebraMap R T)).a₄ = 0 ∧
      (W.map (algebraMap R T)).a₆ = 0 := by
  change algebraMap R T W.a₃ = 0 ∧ algebraMap R T W.a₄ = 0 ∧ algebraMap R T W.a₆ = 0
  constructor
  · rw [← f.commutes, show algebraMap R S W.a₃ = 0 from h3, map_zero]
  constructor
  · rw [← f.commutes, show algebraMap R S W.a₄ = 0 from h4, map_zero]
  · rw [← f.commutes, show algebraMap R S W.a₆ = 0 from h6, map_zero]

end FLT.Mazur.WeierstrassIntegralChart
