/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticExtensionPrimeSubgroup
public import FLT.Mazur.PadicValuationArithmetic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Retaining rational point maps in p-adic minimal equations

The transport is the actual field embedding followed by the inverse generic
variable change and the affine-to-projective equivalence. Its injectivity
preserves an entire specified rational subgroup, not just a chosen generator.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing

variable (q : ℕ) [Fact q.Prime] [DecidableEq ℚ_[q]]
  (E : WeierstrassCurve ℚ) [E.IsElliptic]
  (W : WeierstrassCurve (padicIntegerSubring q)) (C : VariableChange ℚ_[q])
  (hC : C • E.map (algebraMap ℚ ℚ_[q]) =
    W.map (algebraMap (padicIntegerSubring q) ℚ_[q]))

/-- The original rational points mapped into the specified local generic model. -/
def rationalPadicProjectiveHom :
    (E⁄ℚ).Point →+ (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).toProjective.Point :=
  (Projective.Point.toAffineAddEquiv _).symm.toAddMonoidHom.comp
    (ellipticExtensionPointHom (K := ℚ) E W C hC)

/-- The exact coordinate transport is injective on all original rational points. -/
theorem rationalPadicProjectiveHom_injective :
    Function.Injective (rationalPadicProjectiveHom q E W C hC) :=
  (Projective.Point.toAffineAddEquiv _).symm.injective.comp
    (ellipticExtensionPointHom_injective E W C hC)

/-- Exact orders are preserved by the actual local coordinate transport. -/
theorem rationalPadicProjectiveHom_addOrderOf (P : (E⁄ℚ).Point) :
    addOrderOf (rationalPadicProjectiveHom q E W C hC P) = addOrderOf P :=
  addOrderOf_injective _ (rationalPadicProjectiveHom_injective q E W C hC) P

/-- Choose a minimal integral equation and retain the concrete generic variable change. -/
theorem exists_rational_padic_minimal_transport :
    ∃ (W : WeierstrassCurve (padicIntegerSubring q)) (C : VariableChange ℚ_[q])
      (hC : C • E.map (algebraMap ℚ ℚ_[q]) =
        W.map (algebraMap (padicIntegerSubring q) ℚ_[q])),
      IsMinimal (padicIntegerSubring q)
        (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])) ∧
      Function.Injective (rationalPadicProjectiveHom q E W C hC) := by
  let A := padicIntegerSubring q
  let V := E.map (algebraMap ℚ ℚ_[q])
  obtain ⟨C, hmin⟩ := V.exists_isMinimal A
  let _ := hmin
  let W := (C • V).integralModel A
  have hw : W.map (algebraMap A ℚ_[q]) = C • V := baseChange_integralModel_eq A (C • V)
  exact ⟨W, C, hw.symm, hw.symm ▸ hmin,
    rationalPadicProjectiveHom_injective q E W C hw.symm⟩

end FLT.Mazur
