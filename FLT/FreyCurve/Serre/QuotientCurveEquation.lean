/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientCurve

/-!
# Retaining the descended Vélu equation

The target is identified with the coefficient-sum curve after base change.
The finite enumeration is fixed internally, so downstream statements need
neither a chosen enumeration nor an arbitrary additive-map target.
-/

@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) (hn : 0 < n)
variable (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n)

/-- The rational target has precisely the descended Vélu coefficients for `ker q`. -/
def TorsionQuotientEquation (E' : WeierstrassCurve ℚ) : Prop :=
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  E'.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    curve (E⁄(AlgebraicClosure ℚ)) (torsionKernel E n q)

/-- The coefficient equation uniquely determines the rational target. -/
theorem TorsionQuotientEquation.unique {E₁ E₂ : WeierstrassCurve ℚ}
    (h₁ : TorsionQuotientEquation E n hn q E₁)
    (h₂ : TorsionQuotientEquation E n hn q E₂) : E₁ = E₂ := by
  exact WeierstrassCurve.map_injective (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    (h₁.trans h₂.symm)

/-- Oddness proves ellipticity of any rational solution of the coefficient equation. -/
theorem TorsionQuotientEquation.isElliptic (hodd : Odd n) {E' : WeierstrassCurve ℚ}
    (h : TorsionQuotientEquation E n hn q E') : E'.IsElliptic := by
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  exact torsionQuotient_isElliptic E n q hodd E' h

/-- The quotient construction retains its coefficient equation and its rational maps. -/
theorem exists_torsionQuotient_equation_maps (hodd : Odd n)
    (hq : Function.Surjective q)
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation n g t) = q t) :
    ∃ E' : WeierstrassCurve ℚ, TorsionQuotientEquation E n hn q E' ∧ E'.IsElliptic ∧
      ∃ (φ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point) (f : ZMod n →+ (E'⁄ℚ).Point),
        (∀ a, φ a = 0 → n • a = 0) ∧ Function.Injective f := by
  classical
  let _ : (E⁄(AlgebraicClosure ℚ)).IsElliptic := by
    change (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
    infer_instance
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  obtain ⟨E', hcurve⟩ := exists_torsionQuotient_curve E n q hn hfixed
  have hadd := pointMap_add_of_curve_eq (E⁄(AlgebraicClosure ℚ))
    (torsionKernel E n q) (torsionKernel_ne_neg E n q hodd)
    (E'.map (algebraMap ℚ (AlgebraicClosure ℚ))) hcurve
    (torsionKernel_landing E n q hodd E' hcurve)
  obtain ⟨hE', hm⟩ := rational_maps_of_odd_velu E n q hodd hq hfixed E' hcurve
    (fun P Q _ _ _ ↦ hadd P Q)
  exact ⟨E', hcurve, hE', hm⟩

end WeierstrassCurve.Velu
