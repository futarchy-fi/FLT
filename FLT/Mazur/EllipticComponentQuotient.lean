/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionKernel
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The quotient by nonsingular reduction

For a minimal integral equation over a complete discrete valuation ring this
is the rational component quotient E(K)/E₀(K). The construction itself works
over any valuation subring. Finiteness and the Kodaira bounds require separate
proofs about the equation; no component classification is assumed here.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Generic points modulo the actual nonsingular-reduction subgroup. -/
abbrev EllipticComponentQuotient :=
  (W.map (algebraMap A K)).toProjective.Point ⧸ ellipticE0 A W

/-- The class of a generic point modulo nonsingular reduction. -/
noncomputable def ellipticComponentHom :
    (W.map (algebraMap A K)).toProjective.Point →+ EllipticComponentQuotient A W :=
  QuotientAddGroup.mk' (ellipticE0 A W)

/-- Every rational component class is represented by a rational point. -/
theorem ellipticComponentHom_surjective : Function.Surjective (ellipticComponentHom A W) :=
  QuotientAddGroup.mk'_surjective _

/-- The zero class consists exactly of points with nonsingular reduction. -/
@[simp] theorem ellipticComponentHom_eq_zero
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    ellipticComponentHom A W P = 0 ↔ SmoothReduction A W P :=
  QuotientAddGroup.eq_zero_iff P

/-- The kernel of the rational component homomorphism is E₀. -/
@[simp] theorem ellipticComponentHom_ker :
    (ellipticComponentHom A W).ker = ellipticE0 A W :=
  QuotientAddGroup.ker_mk' _

/-- Two points give the same class exactly when their difference reduces smoothly. -/
theorem ellipticComponentHom_eq_iff
    (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    ellipticComponentHom A W P = ellipticComponentHom A W Q ↔
      SmoothReduction A W (P - Q) :=
  QuotientAddGroup.eq_iff_sub_mem

/-- An annihilated component class is equivalent to smooth reduction of the multiple. -/
theorem nsmul_ellipticComponentHom_eq_zero_iff (n : ℕ)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    n • ellipticComponentHom A W P = 0 ↔ SmoothReduction A W (n • P) := by
  rw [← map_nsmul, ellipticComponentHom_eq_zero]

end FLT.Mazur
