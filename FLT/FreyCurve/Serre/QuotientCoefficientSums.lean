/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientEquationCoefficients

/-!
# Rational Vélu coefficient sums

The target equation determines rational values of both geometric kernel sums.
The formulas below retain those values without a choice of descent witnesses.
-/

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

/-- The rational value of the first coefficient sum, recovered from the target. -/
def rationalT (E E' : WeierstrassCurve ℚ) : ℚ := (E.a₄ - E'.a₄) / 5

/-- The rational value of the second coefficient sum, recovered from the target. -/
def rationalW (E E' : WeierstrassCurve ℚ) : ℚ :=
  (E.a₆ - E'.a₆ - E.b₂ * rationalT E E') / 7

/-- The fourth coefficient is recovered from the rational first sum. -/
theorem a₄_eq_rationalT (E E' : WeierstrassCurve ℚ) :
    E'.a₄ = E.a₄ - 5 * rationalT E E' := by
  unfold rationalT
  ring

/-- The sixth coefficient is recovered from the two rational sums. -/
theorem a₆_eq_rationalW (E E' : WeierstrassCurve ℚ) :
    E'.a₆ = E.a₆ - E.b₂ * rationalT E E' - 7 * rationalW E E' := by
  unfold rationalW
  ring

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {n : ℕ} {hn : 0 < n}
variable {q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n}
variable {E' : WeierstrassCurve ℚ} (h : TorsionQuotientEquation E n hn q E')

include h

/-- The rational first sum maps to the actual geometric kernel sum. -/
theorem TorsionQuotientEquation.rationalT_map :
    let _ : Fintype (torsionKernel E n q) :=
      @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
    algebraMap ℚ (AlgebraicClosure ℚ) (rationalT E E') =
      t (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) := by
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  have ha := congrArg WeierstrassCurve.a₄ h
  change algebraMap ℚ (AlgebraicClosure ℚ) E'.a₄ =
    algebraMap ℚ (AlgebraicClosure ℚ) E.a₄ - 5 *
      t (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) at ha
  simp only [rationalT, map_div₀, map_sub, map_ofNat, ha]
  ring

/-- The rational second sum maps to the actual geometric kernel sum. -/
theorem TorsionQuotientEquation.rationalW_map :
    let _ : Fintype (torsionKernel E n q) :=
      @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
    algebraMap ℚ (AlgebraicClosure ℚ) (rationalW E E') =
      w (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) := by
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  have ha := congrArg WeierstrassCurve.a₆ h
  change algebraMap ℚ (AlgebraicClosure ℚ) E'.a₆ =
    algebraMap ℚ (AlgebraicClosure ℚ) E.a₆ -
      (E⁄(AlgebraicClosure ℚ)).b₂ * t (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) -
      7 * w (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q) at ha
  have hb : algebraMap ℚ (AlgebraicClosure ℚ) E.b₂ =
      (E⁄(AlgebraicClosure ℚ)).b₂ := (map_b₂ _ _).symm
  simp only [rationalW, map_div₀, map_sub, map_mul, map_ofNat, ha, hb, h.rationalT_map]
  ring

end WeierstrassCurve.Velu
