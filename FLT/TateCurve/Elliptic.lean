/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurve

/-!
# Ellipticity of the Tate curve

The discriminant of the integral formal Tate equation is `q + O(q²)`.
Its evaluation therefore has valuation `|q|` on the punctured open unit disc,
which proves that the Tate curve is elliptic in every characteristic.
-/

@[expose] public section

open scoped PowerSeries
open ValuativeRel

namespace TateCurve

/-- The Tate equation with integral formal coefficients. -/
noncomputable def formalCurve : WeierstrassCurve ℤ⟦X⟧ := ⟨1, 0, 0, a₄Formal, a₆Formal⟩

/-- The constant coefficient of the formal Tate discriminant vanishes. -/
theorem constantCoeff_formalCurve_Δ : PowerSeries.constantCoeff formalCurve.Δ = 0 := by
  simp [formalCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, a₄Formal, a₆Formal, sInt]

/-- The linear coefficient of the formal Tate discriminant is one. -/
theorem coeff_one_formalCurve_Δ : PowerSeries.coeff 1 formalCurve.Δ = 1 := by
  norm_num [formalCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, PowerSeries.coeff_one_mul,
    PowerSeries.coeff_one_pow, a₄Formal, a₆Formal, sInt]

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Evaluation of integral power series on the open unit disc as a ring homomorphism. -/
noncomputable def evalIntHom (q : K) (hq : valuation K q < 1) : ℤ⟦X⟧ →+* K where
  toFun := evalInt q
  map_zero' := by simp [evalInt]
  map_one' := by simp [evalInt]
  map_add' F G := evalInt_add (summable_evalInt q hq F) (summable_evalInt q hq G)
  map_mul' := evalInt_mul q hq

/-- Evaluation of the formal Tate equation gives the analytic Tate curve. -/
theorem map_formalCurve (q : K) (hq : valuation K q < 1) :
    formalCurve.map (evalIntHom q hq) = WeierstrassCurve.tateCurve q := by
  ext <;> simp [formalCurve, WeierstrassCurve.map, WeierstrassCurve.tateCurve,
    WeierstrassCurve.tateA₄_eq_evalInt q hq, WeierstrassCurve.tateA₆_eq_evalInt q hq] <;> rfl

/-- The Tate discriminant has the same valuation as its nonzero parameter. -/
theorem valuation_tateCurve_Δ {q : K} (hq0 : q ≠ 0) (hq : valuation K q < 1) :
    valuation K (WeierstrassCurve.tateCurve q).Δ = valuation K q := by
  rw [← map_formalCurve q hq, WeierstrassCurve.map_Δ]
  exact valuation_evalInt_eq q hq0 hq constantCoeff_formalCurve_Δ coeff_one_formalCurve_Δ

/-- The Tate discriminant is nonzero on the punctured open unit disc. -/
theorem tateCurve_Δ_ne_zero {q : K} (hq0 : q ≠ 0) (hq : valuation K q < 1) :
    (WeierstrassCurve.tateCurve q).Δ ≠ 0 := by
  intro h
  have hv := valuation_tateCurve_Δ hq0 hq
  rw [h, map_zero] at hv
  exact ((valuation K).ne_zero_iff.mpr hq0) hv.symm

/-- The Tate curve is elliptic for every nonzero parameter of valuation less than one. -/
theorem tateCurve_isElliptic {q : K} (hq0 : q ≠ 0) (hq : valuation K q < 1) :
    (WeierstrassCurve.tateCurve q).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (tateCurve_Δ_ne_zero hq0 hq)⟩

end TateCurve
