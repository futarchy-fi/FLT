/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Uniformization
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!+# Tate coordinates on the quotient by powers of the parameter

Periodicity makes the two coordinate functions independent of the chosen
representative in `Kˣ/q^ℤ`. Their values on the identity class are junk affine
coordinates: a point-valued uniformization must send that class to infinity.
-/

@[expose] public section

namespace TateCurve

variable {K : Type*} [Field K] [TopologicalSpace K]

/-- The two Tate coordinates descend to `Kˣ/q^ℤ`. This is a map to pairs of field
elements; proving the curve equation is a separate prerequisite for a map to points. -/
noncomputable def quotientCoordinates (q : Kˣ) : Kˣ ⧸ Subgroup.zpowers q → K × K :=
  Quotient.lift (fun u : Kˣ ↦ (tateX (u : K) (q : K), tateY (u : K) (q : K))) (by
    intro u v huv
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.leftRel_apply.mp huv)
    have hv : v = q ^ m * u := by
      rw [hm]
      simp [mul_comm]
    subst v
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val,
      tateX_zpow_mul _ (Units.ne_zero q), tateY_zpow_mul _ (Units.ne_zero q)])

/-- Evaluation of the quotient coordinate map on a representative. -/
@[simp]
theorem quotientCoordinates_mk (q u : Kˣ) :
    quotientCoordinates q (u : Kˣ ⧸ Subgroup.zpowers q) =
      (tateX (u : K) (q : K), tateY (u : K) (q : K)) := rfl

omit [TopologicalSpace K] in
/-- Every nonidentity quotient class has nonvanishing coordinate denominators. -/
theorem denominators_ne_zero_of_mk_ne_one (q u : Kˣ)
    (hu : (u : Kˣ ⧸ Subgroup.zpowers q) ≠ 1) (n : ℤ) :
    1 - (q : K) ^ n * (u : K) ≠ 0 :=
  one_sub_zpow_mul_ne_zero q u (fun h ↦ hu ((QuotientGroup.eq_one_iff u).mpr h)) n

end TateCurve
