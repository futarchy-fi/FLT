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
end TateCurve
