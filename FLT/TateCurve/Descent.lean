/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Naturality
public import Mathlib.FieldTheory.Galois.Basic
/-!
# Descent of Tate parameters

Injectivity modulo powers of the Tate parameter, together with equality of
valuations, gives equality of unit representatives. Consequently, a Galois-fixed
Tate point over a finite Galois extension has a parameter in the base field,
provided the automorphisms are continuous and preserve its valuation.
-/

@[expose] public section

open ValuativeRel
open scoped WeierstrassCurve.Affine
namespace TateCurve
variable {K : Type*} [Field K] [ValuativeRel K]
/-- Equal quotient representatives with equal valuation are equal. -/
theorem eq_of_quotient_eq_of_valuation_eq (q u v : Kˣ)
    (hq : valuation K (q : K) < 1)
    (h : (u : Kˣ ⧸ Subgroup.zpowers q) = v)
    (hv : valuation K (u : K) = valuation K (v : K)) : u = v := by
  have hm : u / v ∈ Subgroup.zpowers q := QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hm
  have hpow : valuation K (q : K) ^ n = 1 := by
    have he := congrArg (fun a : Kˣ ↦ valuation K (a : K)) hn
    simpa only [Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val, map_zpow₀,
      map_div₀, hv, div_self ((valuation K).ne_zero_iff.mpr v.ne_zero)] using he
  have hn0 : n = 0 := (zpow_right_strictAnti₀
    (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr q.ne_zero)) hq).injective
      (hpow.trans (zpow_zero _).symm)
  simpa only [hn0, zpow_zero, eq_comm, div_eq_one] using hn
end TateCurve
namespace TateCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [DecidableEq L]
/-- A valuation-preserving automorphism fixes a parameter if it fixes its Tate point. -/
theorem unit_fixed_of_uniformizationPointOver_fixed (q : Kˣ)
    (hq : valuation K (q : K) < 1) (σ : L ≃ₐ[K] L) (hσ : Continuous σ)
    (u : Lˣ) (hv : valuation L (σ (u : L)) = valuation L (u : L))
    (hp : WeierstrassCurve.Affine.Point.map σ.toAlgHom
      (uniformizationPointOver L q hq u) = uniformizationPointOver L q hq u) :
    σ (u : L) = u := by
  rw [uniformizationPointOver_galois σ hσ] at hp
  have he := eq_of_quotient_eq_of_valuation_eq
    (Units.map (algebraMap K L).toMonoidHom q)
    (Units.map σ.toAlgHom.toRingHom.toMonoidHom u) u
    (valuation_algebraMap_lt_one hq)
    ((uniformizationPointOver_eq_iff L q hq _ _).mp hp) hv
  exact congrArg Units.val he

/-- In a finite Galois extension, a fixed Tate point has a parameter in the base field. -/
theorem exists_unit_of_fixed_uniformizationPointOver [FiniteDimensional K L] [IsGalois K L]
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ)
    (hc : ∀ σ : L ≃ₐ[K] L, Continuous σ)
    (hv : ∀ σ : L ≃ₐ[K] L, valuation L (σ (u : L)) = valuation L (u : L))
    (hp : ∀ σ : L ≃ₐ[K] L, WeierstrassCurve.Affine.Point.map σ.toAlgHom
      (uniformizationPointOver L q hq u) = uniformizationPointOver L q hq u) :
    ∃ v : Kˣ, Units.map (algebraMap K L).toMonoidHom v = u := by
  have hm : (u : L) ∈ Set.range (algebraMap K L) :=
    (IsGalois.mem_range_algebraMap_iff_fixed _).mpr fun σ ↦
      unit_fixed_of_uniformizationPointOver_fixed q hq σ (hc σ) u (hv σ) (hp σ)
  obtain ⟨v, he⟩ := hm
  have hv0 : v ≠ 0 := by
    intro h
    exact u.ne_zero (he.symm.trans (by simp [h]))
  exact ⟨Units.mk0 v hv0, Units.ext he⟩
/-- A parameter whose abscissa is that of a rational point has a Galois-fixed Tate point. -/
theorem uniformizationPointOver_fixed_of_tateX_eq
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ)
    (hu : u ∉ Subgroup.zpowers (Units.map (algebraMap K L).toMonoidHom q))
    {x y : K} (hxy : (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y)
    (hx : tateX (u : L) (algebraMap K L q) = algebraMap K L x)
    (σ : L ≃ₐ[K] L) :
    WeierstrassCurve.Affine.Point.map σ.toAlgHom (uniformizationPointOver L q hq u) =
      uniformizationPointOver L q hq u := by
  let E := WeierstrassCurve.tateCurve (q : K)
  have hP : (E⁄L).Nonsingular (algebraMap K L x) (algebraMap K L y) :=
    (E.toAffine.map_nonsingular (algebraMap K L).injective x y).mpr hxy
  have hQ := tateCoordinates_nonsingular (Units.map (algebraMap K L).toMonoidHom q) u
    (valuation_algebraMap_lt_one hq) hu
  have hQ' : (E⁄L).Nonsingular (tateX (u : L) (algebraMap K L q))
      (tateY (u : L) (algebraMap K L q)) := by
    simpa [E, WeierstrassCurve.tateCurve_baseChange (q : K) hq] using hQ
  have he : uniformizationPointOver L q hq u = .some _ _ hQ' := by
    simp only [uniformizationPointOver, uniformizationPoint, dite_eq_right hu]
    erw [WeierstrassCurve.Affine.Point.equivOfEq_some]
    rfl
  have hfixed : WeierstrassCurve.Affine.Point.map σ.toAlgHom (.some _ _ hP) =
      .some _ _ hP := by
    simp only [WeierstrassCurve.Affine.Point.map_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨σ.commutes x, σ.commutes y⟩
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := hQ') (h₂ := hP)).mp hx with h | h
  · rw [he, h, hfixed]
  · rw [he, h, map_neg, hfixed]
omit [DecidableEq L] in
/-- A parameter above a rational abscissa descends through a finite Galois extension. -/
theorem exists_unit_of_tateX_eq [FiniteDimensional K L] [IsGalois K L]
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ)
    (hu : u ∉ Subgroup.zpowers (Units.map (algebraMap K L).toMonoidHom q))
    {x y : K} (hxy : (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y)
    (hx : tateX (u : L) (algebraMap K L q) = algebraMap K L x)
    (hc : ∀ σ : L ≃ₐ[K] L, Continuous σ)
    (hv : ∀ σ : L ≃ₐ[K] L, valuation L (σ (u : L)) = valuation L (u : L)) :
    ∃ v : Kˣ, Units.map (algebraMap K L).toMonoidHom v = u := by
  classical
  exact exists_unit_of_fixed_uniformizationPointOver q hq u hc hv
    (uniformizationPointOver_fixed_of_tateX_eq q hq u hu hxy hx)

end TateCurve
