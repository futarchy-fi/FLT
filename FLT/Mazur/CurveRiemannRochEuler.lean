/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCurveGenus
public import FLT.Mazur.CurvePositiveDegreeSections

/-!
# The Euler form of Riemann–Roch

With degree defined by Euler characteristic, constant global functions give
h⁰(L) − h¹(L) = deg(L) + 1 − g. The resulting lower bound produces an actual
nonzero section in degree at least g. This is not the duality form of
Riemann–Roch and does not yet assert large-degree H¹ vanishing.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim X = 1) (hc : HasConstantGlobalSections f)

/-- The actual structure-sheaf Euler characteristic is one minus the genus. -/
theorem curveEulerCharacteristic_structure_eq_one_sub_genus :
    curveEulerCharacteristic f (structureUnitModule X) = 1 - curveGenus f hd hc := by
  unfold curveEulerCharacteristic
  rw [(moduleScalarHUnitEquiv f 0).finrank_eq,
    (moduleScalarHUnitEquiv f 1).finrank_eq,
    finrank_H0_of_constantGlobalSections f hc]
  rfl

/-- The Euler form of Riemann–Roch for the actual cohomological degree. -/
theorem curve_riemannRoch_euler (L : X.Modules) :
    (Module.finrank k (ModuleScalarH f L 0) : ℤ) -
        Module.finrank k (ModuleScalarH f L 1) =
      curveSheafDegree f L + 1 - curveGenus f hd hc := by
  have h := curveEulerCharacteristic_structure_eq_one_sub_genus f hd hc
  unfold curveSheafDegree curveEulerCharacteristic at *
  omega

/-- Riemann–Roch bounds the dimension of sections from below. -/
theorem curve_h0_lower_bound (L : X.Modules) :
    curveSheafDegree f L + 1 - curveGenus f hd hc ≤
      (Module.finrank k (ModuleScalarH f L 0) : ℤ) := by
  have := curve_riemannRoch_euler f hd hc L
  omega

/-- Degree at least the genus gives an actual nonzero global section. -/
theorem exists_nonzero_section_of_degree_ge_genus (L : X.Modules)
    (hL : (curveGenus f hd hc : ℤ) ≤ curveSheafDegree f L) :
    ∃ s : Γ(L, ⊤), s ≠ 0 := by
  apply exists_nonzero_section_of_h0_pos f L
  have := curve_h0_lower_bound f hd hc L
  omega

/-- When H¹ vanishes, the section dimension has its expected value. -/
theorem curve_h0_eq_of_h1_vanishing (L : X.Modules)
    [Subsingleton (ModuleScalarH f L 1)] :
    (Module.finrank k (ModuleScalarH f L 0) : ℤ) =
      curveSheafDegree f L + 1 - curveGenus f hd hc := by
  simpa only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_zero] using
    curve_riemannRoch_euler f hd hc L

end FLT.Mazur.FCurve
