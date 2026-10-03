/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Integer principal filtration inside a fraction field -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The actual submodule t^n R inside the fraction field, including negative n. -/
def fractionalPrincipalFiltration (t : R) (n : ℤ) : Submodule R K :=
  Submodule.span R {(algebraMap R K t) ^ n}

/-- Multiplication by t^n identifies the actual filtration submodule with its coefficients. -/
def fractionalPrincipalEquiv {t : R} (ht : t ≠ 0) (n : ℤ) :
    R ≃ₗ[R] fractionalPrincipalFiltration (K := K) t n :=
  LinearEquiv.toSpanNonzeroSingleton R K ((algebraMap R K t) ^ n)
    (zpow_ne_zero n ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ht))

/-- The coefficient map is the original field multiplication. -/
theorem fractionalPrincipalEquiv_coe {t : R} (ht : t ≠ 0) (n : ℤ) (a : R) :
    (fractionalPrincipalEquiv (K := K) ht n a : K) =
      algebraMap R K a * (algebraMap R K t) ^ n := by
  exact (congrArg Subtype.val (LinearEquiv.toSpanNonzeroSingleton_apply R K
    ((algebraMap R K t) ^ n) _ a)).trans (Algebra.smul_def a _)

omit [IsDomain R] in
/-- The next integer level is contained in the current level. -/
theorem fractionalPrincipalFiltration_succ_le {t : R} (ht : t ≠ 0) (n : ℤ) :
    fractionalPrincipalFiltration (K := K) t (n + 1) ≤ fractionalPrincipalFiltration t n := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  refine Submodule.mem_span_singleton.mpr ⟨t, ?_⟩
  simp only [Algebra.smul_def]
  rw [zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ht), zpow_one, mul_comm]

omit [IsDomain R] in
/-- Multiplication of actual filtration representatives adds their integer levels. -/
theorem fractionalPrincipalFiltration_mul_mem (t : R) (ht : t ≠ 0) (m n : ℤ)
    {x y : K} (hx : x ∈ fractionalPrincipalFiltration t m)
    (hy : y ∈ fractionalPrincipalFiltration t n) :
    x * y ∈ fractionalPrincipalFiltration t (m + n) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  refine Submodule.mem_span_singleton.mpr ⟨a * b, ?_⟩
  simp only [Algebra.smul_def]
  rw [map_mul, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ht)]
  ring

end PadicHodgeTheory
