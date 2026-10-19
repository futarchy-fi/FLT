/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientCoefficientSums

/-!
# Invariants of the descended Vélu equation

These identities express the changes in c₄ and c₆ in terms of the retained
rational kernel sums. They are equations for the actual descended target.
-/

@[expose] public section

namespace WeierstrassCurve.Velu.TorsionQuotientEquation

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {n : ℕ} {hn : 0 < n}
variable {q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n}
variable {E' : WeierstrassCurve ℚ} (h : TorsionQuotientEquation E n hn q E')

include h

/-- The descended target's b₄ changes by ten times the rational first sum. -/
theorem b₄ : E'.b₄ = E.b₄ - 10 * rationalT E E' := by
  simp only [WeierstrassCurve.b₄, h.a₁, h.a₃, a₄_eq_rationalT E E']
  ring

/-- The descended target's b₆ retains both rational kernel sums. -/
theorem b₆ : E'.b₆ = E.b₆ - 4 * E.b₂ * rationalT E E' - 28 * rationalW E E' := by
  simp only [WeierstrassCurve.b₆, h.a₃, a₆_eq_rationalW E E']
  ring

/-- The c₄ change is integral even though the defining all-points sums used halves. -/
theorem c₄ : E'.c₄ = E.c₄ + 240 * rationalT E E' := by
  simp only [WeierstrassCurve.c₄, h.b₂, h.b₄]
  ring

/-- The exact c₆ change of the descended equation. -/
theorem c₆ : E'.c₆ = E.c₆ + 504 * E.b₂ * rationalT E E' + 6048 * rationalW E E' := by
  simp only [WeierstrassCurve.c₆, h.b₂, h.b₄, h.b₆]
  ring

end WeierstrassCurve.Velu.TorsionQuotientEquation
