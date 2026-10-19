/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientCoefficientSums
public import FLT.FreyCurve.Serre.VeluIntegralSums
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral descent of the rational kernel sums

Integrality of the geometric abscissae passes to the paired sums and then to
the rational sums. This keeps the exact quotient equation throughout descent.
The coordinate hypothesis is explicit; local torsion lemmas supply it only
after the kernel has been realized in the relevant complete local field.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu.TorsionQuotientEquation

variable {R : Type*} [CommRing R] [Algebra R ℚ]
variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {n : ℕ} {hn : 0 < n}
variable {q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n}
variable {E' : WeierstrassCurve ℚ} (h : TorsionQuotientEquation E n hn q E')

include h

/-- Integral kernel abscissae descend to integral rational t and w, without inverting two. -/
theorem rational_sums_isIntegral (hodd : Odd n)
    (h₂ : IsIntegral R E.b₂) (h₄ : IsIntegral R E.b₄) (h₆ : IsIntegral R E.b₆)
    (hx : ∀ Q : torsionKernel E n q, Q ≠ 0 → IsIntegral R (xCoord Q.val)) :
    IsIntegral R (rationalT E E') ∧ IsIntegral R (rationalW E E') := by
  classical
  let _ : Fintype (torsionKernel E n q) :=
    @Fintype.ofFinite _ (torsionKernel_finite E n q hn)
  let f : ℚ →ₐ[R] AlgebraicClosure ℚ := IsScalarTower.toAlgHom R ℚ (AlgebraicClosure ℚ)
  let S := (integralClosure R (AlgebraicClosure ℚ)).toSubring
  have hb₂ : (E⁄(AlgebraicClosure ℚ)).b₂ ∈ S := by
    change IsIntegral R ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).b₂)
    rw [map_b₂]
    exact (isIntegral_algHom_iff f f.injective).mpr h₂
  have hb₄ : (E⁄(AlgebraicClosure ℚ)).b₄ ∈ S := by
    change IsIntegral R ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).b₄)
    rw [map_b₄]
    exact (isIntegral_algHom_iff f f.injective).mpr h₄
  have hb₆ : (E⁄(AlgebraicClosure ℚ)).b₆ ∈ S := by
    change IsIntegral R ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).b₆)
    rw [map_b₆]
    exact (isIntegral_algHom_iff f f.injective).mpr h₆
  constructor
  · apply (isIntegral_algHom_iff f f.injective).mp
    change IsIntegral R (algebraMap ℚ (AlgebraicClosure ℚ) (rationalT E E'))
    rw [h.rationalT_map]
    exact t_mem_subring _ _ (torsionKernel_ne_neg E n q hodd) S hb₂ hb₄ hx
  · apply (isIntegral_algHom_iff f f.injective).mp
    change IsIntegral R (algebraMap ℚ (AlgebraicClosure ℚ) (rationalW E E'))
    rw [h.rationalW_map]
    exact w_mem_subring _ _ (torsionKernel_ne_neg E n q hodd) S hb₂ hb₄ hb₆ hx

/-- The changed rational coefficients are integral once the actual kernel sums are. -/
theorem a₄_a₆_isIntegral (hodd : Odd n)
    (h₂ : IsIntegral R E.b₂) (h₄ : IsIntegral R E.b₄) (h₆ : IsIntegral R E.b₆)
    (ha₄ : IsIntegral R E.a₄) (ha₆ : IsIntegral R E.a₆)
    (hx : ∀ Q : torsionKernel E n q, Q ≠ 0 → IsIntegral R (xCoord Q.val)) :
    IsIntegral R E'.a₄ ∧ IsIntegral R E'.a₆ := by
  obtain ⟨ht, hw⟩ := h.rational_sums_isIntegral hodd h₂ h₄ h₆ hx
  rw [a₄_eq_rationalT E E', a₆_eq_rationalW E E']
  exact ⟨ha₄.sub ((isIntegral_natCast (R := R) 5).mul ht),
    (ha₆.sub (h₂.mul ht)).sub ((isIntegral_natCast (R := R) 7).mul hw)⟩

end WeierstrassCurve.Velu.TorsionQuotientEquation
