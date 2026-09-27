/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Descent
public import FLT.TateCurve.FiniteExtension
public import FLT.TateCurve.QuadraticLift
public import Mathlib.Algebra.Polynomial.SpecificDegree
/-!
# Splitting the symmetric Tate quadratics

A root of a separable parameter polynomial lies in a finite Galois local-field
extension. Its Tate abscissa is rational, so both possible ordinates are rational.
Naturality and injectivity then descend the parameter to the base field.
This proves boundary lifting and interior lifting when the derivative is nonzero.
-/

@[expose] public section

open ValuativeRel Polynomial
universe u
namespace TateCurve
variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
/-- A separable polynomial has a rational root if all its roots are Tate parameters
above the abscissa of a rational point. -/
theorem exists_root_of_separable_of_tateX (q : Kˣ) (hq : valuation K (q : K) < 1)
    {x y : K} (hxy : (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y)
    (f : K[X]) (hsep : f.Separable) (hdeg : f.natDegree ≠ 0)
    (h : ∀ {L : Type u} [Field L] [ValuativeRel L] [TopologicalSpace L]
      [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L],
      Continuous (algebraMap K L) → ∀ a : L, aeval a f = 0 →
      ∃ u : Lˣ, (u : L) = a ∧
        u ∉ Subgroup.zpowers (Units.map (algebraMap K L).toMonoidHom q) ∧
        tateX (u : L) (algebraMap K L q) = algebraMap K L x) :
    ∃ a : K, f.eval a = 0 := by
  classical
  let L := f.SplittingField
  obtain ⟨v, top, hloc, hext, hc, hσ⟩ := exists_localField_extension K L
  let :=  v
  let :=  top
  let :=  hloc
  let :=  hext
  have : IsGalois K L := IsGalois.of_separable_splitting_field hsep
  obtain ⟨a, ha⟩ := (SplittingField.splits f).exists_eval_eq_zero
    (by
      intro hd
      have hn := natDegree_eq_of_degree_eq_some hd
      exact hdeg (by convert! hn using 1; simp only [natDegree_map]))
  have har : aeval a f = 0 := by simpa only [eval_map, aeval_def] using ha
  obtain ⟨u, hu, hmem, hx⟩ := h hc a har
  obtain ⟨w, hw⟩ := exists_unit_of_tateX_eq q hq u hmem hxy hx
    (fun σ ↦ (hσ σ).1) (fun σ ↦ (hσ σ).2 u)
  refine ⟨w, (algebraMap K L).injective ?_⟩
  have he : algebraMap K L (w : K) = a := (congrArg Units.val hw).trans hu
  simpa only [← eval₂_at_apply, ← aeval_def, he, map_zero] using har
end TateCurve
open Polynomial
namespace TateCurve
variable {K : Type*} [Field K]
/-- The polynomial defining a symmetric Tate parameter. -/
noncomputable def parameterQuadratic (t a : K) : K[X] := Polynomial.X ^ 2 - C t * Polynomial.X + C a
/-- The symmetric parameter polynomial has degree two. -/
theorem natDegree_parameterQuadratic (t a : K) : (parameterQuadratic t a).natDegree = 2 := by
  convert natDegree_quadratic (a := (1 : K)) (b := -t) (c := a) one_ne_zero using 1
  · simp [parameterQuadratic, sub_eq_add_neg]
/-- A root-free symmetric quadratic with nonzero derivative is separable. -/
theorem separable_parameterQuadratic {t a : K}
    (h : ¬ ∃ u : K, u ^ 2 - t * u + a = 0) (hder : (2 : K) ≠ 0 ∨ t ≠ 0) :
    (parameterQuadratic t a).Separable := by
  have hi : Irreducible (parameterQuadratic t a) :=
    irreducible_of_degree_le_three_of_not_isRoot
      (by simp [natDegree_parameterQuadratic]) (fun u hu ↦ h ⟨u, by
        simpa [IsRoot, parameterQuadratic] using hu⟩)
  apply (separable_iff_derivative_ne_zero hi).mpr
  intro hd
  rcases hder with h2 | ht
  · have he := congrArg (fun p : K[X] ↦ p.coeff 1) hd
    exact h2 (by simpa [parameterQuadratic, derivative_sub, derivative_add, derivative_mul,
      derivative_pow] using he)
  · have he := congrArg (fun p : K[X] ↦ p.coeff 0) hd
    exact ht (by simpa [parameterQuadratic, derivative_sub, derivative_add, derivative_mul,
      derivative_pow] using he)
end TateCurve
open ValuativeRel
namespace TateCurve
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [TopologicalSpace L] [T2Space L]
/-- Continuous field morphisms commute with the convergent paired coordinate series. -/
theorem map_tsum_xPair (f : K →+* L) (hf : Continuous f) {q a t : K}
    (hq : valuation K q < 1) (ha : valuation K a < 1) (ht : valuation K t < 1) :
    f (∑' n : ℕ, xPair (q ^ (2 * n) * a) (q ^ n * t)) =
      ∑' n : ℕ, xPair (f q ^ (2 * n) * f a) (f q ^ n * f t) := by
  rw [(summable_xPair hq ha ht).map_tsum f hf]
  simp only [xPair, map_div₀, map_sub, map_mul, map_add, map_one, map_ofNat, map_pow]
/-- Continuous field morphisms commute with the bounded boundary tail. -/
theorem map_boundaryTail (f : K →+* L) (hf : Continuous f) {q z : K}
    (hq : valuation K q < 1) (hz : valuation K z ≤ 1) :
    f (boundaryTail q z) = boundaryTail (f q) (f z) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hs : valuation K (z + 2) ≤ 1 := (Valuation.map_add _ _ _).trans
    (max_le hz (valuation_natCast_le_one (R := K) 2))
  have hqs : valuation K (q * (z + 2)) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right' hs).trans_lt hq
  have hq2 : valuation K (q ^ 2) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hq (by decide)
  simp only [boundaryTail, map_sub, map_mul, map_ofNat,
    map_tsum_xPair f hf hq hq2 hqs, map_tateCorrection f hf (tendsto_pow_nhds_zero hq),
    map_pow, map_add]
end TateCurve
namespace TateCurve
open ValuativeRel Polynomial
variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
/-- The interior quadratic splits whenever its derivative is nonzero. -/
theorem interior_lift_of_derivative_ne_zero (q : Kˣ) (hq : valuation K (q : K) < 1)
    (x y t : K) (hxy : (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y)
    (ht : valuation K t < 1)
    (hseries : (∑' n : ℕ, xPair ((q : K) ^ (2 * n) * q) ((q : K) ^ n * t)) -
      2 * tateCorrection (q : K) = x)
    (hder : (2 : K) ≠ 0 ∨ t ≠ 0) : ∃ u : K, u ^ 2 - t * u + q = 0 := by
  by_contra hn
  apply hn
  obtain ⟨a, ha⟩ := exists_root_of_separable_of_tateX q hq hxy
    (parameterQuadratic t q) (separable_parameterQuadratic hn hder)
    (by rw [natDegree_parameterQuadratic]; decide) (by
      intro L _ _ _ _ _ _ hf u hu
      have hroot : u ^ 2 - algebraMap K L t * u + algebraMap K L (q : K) = 0 := by
        simpa [parameterQuadratic, map_ofNat] using hu
      have hq' := valuation_algebraMap_lt_one (l := L) hq
      have ht' := valuation_algebraMap_lt_one (l := L) ht
      have hq0 : algebraMap K L (q : K) ≠ 0 := (_root_.map_ne_zero (algebraMap K L)).mpr q.ne_zero
      obtain ⟨hu0, hult, hqu, -⟩ := interior_quadratic_root_bounds hq0 hq' ht' hroot
      refine ⟨Units.mk0 u hu0, rfl, ?_, ?_⟩
      · apply not_mem_zpowers_of_mem_annulus _ (Units.mk0 u hu0) hq'
          (by intro h; change u = 1 at h; simp [h] at hult) _ hult.le
        change valuation L (algebraMap K L (q : K)) < valuation L u
        exact (div_lt_one₀ (zero_lt_iff.mpr ((valuation L).ne_zero_iff.mpr hu0))).mp
          (by simpa only [map_div₀] using hqu)
      · apply tateX_eq_of_interior_quadratic hq0 hq' ht' _ hroot
        let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
        have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
        have he := congrArg (algebraMap K L) hseries
        simpa only [map_sub, map_mul, map_ofNat,
          map_tsum_xPair _ hf hq hq ht,
          map_tateCorrection _ hf (tendsto_pow_nhds_zero hq)] using he)
  exact ⟨a, by simpa [parameterQuadratic] using ha⟩

/-- The boundary quadratic always splits over the original local field. -/
theorem boundary_lift (q : Kˣ) (hq : valuation K (q : K) < 1)
    (x y z : K) (hxy : (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y)
    (hz0 : z ≠ 0) (hz : valuation K z ≤ 1)
    (hseries : 1 / z + boundaryTail (q : K) z = x) :
    ∃ u : K, u ^ 2 - (z + 2) * u + 1 = 0 := by
  by_contra hn
  have hder : (2 : K) ≠ 0 ∨ z + 2 ≠ 0 := by
    by_cases h2 : (2 : K) = 0
    · exact Or.inr (by simpa [h2] using hz0)
    · exact Or.inl h2
  apply hn
  obtain ⟨a, ha⟩ := exists_root_of_separable_of_tateX q hq hxy
    (parameterQuadratic (z + 2) 1) (separable_parameterQuadratic hn hder)
    (by rw [natDegree_parameterQuadratic]; decide) (by
      intro L _ _ _ _ _ _ hf u hu
      have hroot : u ^ 2 - (algebraMap K L z + 2) * u + 1 = 0 := by
        simpa [parameterQuadratic, map_ofNat] using hu
      have hq' := valuation_algebraMap_lt_one (l := L) hq
      have hz' : valuation L (algebraMap K L z) ≤ 1 := by
        simpa only [ValuativeExtension.mapValueGroupWithZero_valuation, map_one] using
          (ValuativeExtension.mapValueGroupWithZero_strictMono (A := K) (B := L)).monotone hz
      have hz0' : algebraMap K L z ≠ 0 := (_root_.map_ne_zero (algebraMap K L)).mpr hz0
      obtain ⟨hu0, hu1, hv, -⟩ := boundary_quadratic_root_bounds hz0' hz' hroot
      refine ⟨Units.mk0 u hu0, rfl, ?_, ?_⟩
      · apply not_mem_zpowers_of_mem_annulus _ (Units.mk0 u hu0) hq' hu1
        · change valuation L (algebraMap K L (q : K)) < valuation L u
          rw [hv]
          exact hq'
        · exact hv.le
      · apply tateX_eq_of_boundary_quadratic
          ((_root_.map_ne_zero (algebraMap K L)).mpr q.ne_zero) hq' hz0' hz' _ hroot
        have he := congrArg (algebraMap K L) hseries
        simpa only [map_add, map_div₀, map_one, map_boundaryTail _ hf hq hz] using he)
  exact ⟨a, by simpa [parameterQuadratic] using ha⟩
end TateCurve
