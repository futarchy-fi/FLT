/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientCurveEquation

/-!
# Rational coefficients fixed by the descended quotient equation

Vélu changes only a₄ and a₆. These equalities descend to the rational target
itself, so the same a₁, a₂, a₃ and b₂ can be used in local calculations.
-/

@[expose] public section

namespace WeierstrassCurve.Velu.TorsionQuotientEquation

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {n : ℕ} {hn : 0 < n}
variable {q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n}
variable {E' : WeierstrassCurve ℚ} (h : TorsionQuotientEquation E n hn q E')

include h

/-- The descended Vélu equation retains the first coefficient over ℚ. -/
theorem a₁ : E'.a₁ = E.a₁ := by
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  exact congrArg WeierstrassCurve.a₁ h

/-- The descended Vélu equation retains the second coefficient over ℚ. -/
theorem a₂ : E'.a₂ = E.a₂ := by
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  exact congrArg WeierstrassCurve.a₂ h

/-- The descended Vélu equation retains the third coefficient over ℚ. -/
theorem a₃ : E'.a₃ = E.a₃ := by
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  exact congrArg WeierstrassCurve.a₃ h

/-- The descended target and original equation have the same b₂ invariant. -/
theorem b₂ : E'.b₂ = E.b₂ := by
  simp only [WeierstrassCurve.b₂, h.a₁, h.a₂]

end WeierstrassCurve.Velu.TorsionQuotientEquation
