/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.TateInertia
public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Inertia at multiplicative reduction

Integral quadratic twisting parameters with unit discriminant split multiplicative
reduction, including in residue characteristic two.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open Polynomial IsLocalRing

universe u

/-- A valuation ring in an algebraically closed field contains a root of every monic quadratic. -/
theorem ValuationSubring.exists_quadratic_root {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) (t n : A) :
    ∃ x : A, x ^ 2 - t * x + n = 0 := by
  let : IsIntegrallyClosed A := (ValuationRing.integers A L).isIntegrallyClosed
  let f : A[X] := X ^ 2 - C t * X + C n
  have hf : f.Monic := by dsimp [f]; monicity!
  have hd : (f.map (algebraMap A L)).degree = 2 := by
    simpa [f, sub_eq_add_neg] using
      (degree_quadratic (b := -(t : L)) (c := (n : L)) (one_ne_zero : (1 : L) ≠ 0))
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap A L)) (by rw [hd]; decide)
  have hint : IsIntegral A x := ⟨f, hf, by simpa [IsRoot, eval_map, aeval_def] using hx⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  apply IsFractionRing.injective A L
  rw [map_zero]
  simpa [f, IsRoot, ← hy] using hx

namespace WeierstrassCurve

/-- A multiplicative equation admits integral twisting parameters with unit
discriminant for which the explicit twisted integral equation is split multiplicative. -/
theorem exists_split_twist_parameters {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) [E.HasMultiplicativeReduction R] :
    ∃ t n : R, IsUnit (t ^ 2 - 4 * n) ∧
      (((E.integralModel R).quadraticTwistOf t n).baseChange K).HasSplitMultiplicativeReduction
        R := by
  let W := E.integralModel R
  let c := residue R W.c₄
  have hc : c ≠ 0 := residue_integralModel_c₄_ne_zero E R
  let b := residue R (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)
  obtain ⟨n, hn⟩ := residue_surjective (-(b / c))
  let t := -W.a₁
  have hA : residue R W.c₄ * residue R t + residue R (W.a₁ * W.c₄) = 0 := by
    simp only [t, map_neg, map_mul]
    ring
  have hB : residue R W.c₄ * residue R n + b = 0 := by
    rw [hn]
    dsimp [c] at *
    field_simp
    ring
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t n hA hB
  have hD : residue R (t ^ 2 - 4 * n) ≠ 0 := by
    intro h
    rw [h, mul_zero, eq_comm, neg_eq_zero] at hkey
    exact residue_integralModel_c₆_ne_zero E R hkey
  let :=  hasMultiplicativeReduction_baseChange_quadraticTwistOf E R t n hD
  exact ⟨t, n, (residue_ne_zero_iff_isUnit _).mp hD,
    hasSplitMultiplicativeReduction_quadraticTwistOf_of_residue E R t n hA hB⟩

/-- A root of the defining quadratic gives an explicit isomorphism from the
quadratic twist to the original equation. -/
theorem quadraticRoot_variableChange_smul {K : Type*} [Field K]
    (E : WeierstrassCurve K) (t n x : K)
    (hx : x ^ 2 - t * x + n = 0) (hw : t - 2 * x ≠ 0) :
    (⟨Units.mk0 (t - 2 * x) hw, 0, -(x * E.a₁),
      -((t - 2 * x) ^ 2 * x * E.a₃)⟩ : VariableChange K) • E.quadraticTwistOf t n = E := by
  have hn : n = t * x - x ^ 2 := by linear_combination hx
  rw [hn, variableChange_def]
  ext <;> simp only [quadraticTwistOf, Units.val_inv_eq_inv_val, Units.val_mk0] <;>
    field_simp <;> ring

/-- An invariant change of variables intertwines the two Galois actions on points. -/
theorem exists_equivariant_pointEquiv_of_variableChange
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [DecidableEq Ω]
    (E E' : WeierstrassCurve K) [E'.IsElliptic]
    (C : VariableChange Ω) (hC : C • E'.baseChange Ω = E.baseChange Ω)
    (σ : Ω ≃ₐ[K] Ω) (hσ : C.map σ.toAlgHom.toRingHom = C) :
    ∃ e : (E⁄Ω).Point ≃+ (E'⁄Ω).Point,
      ∀ P, e (Affine.Point.map σ.toAlgHom P) = Affine.Point.map σ.toAlgHom (e P) := by
  let e : (E⁄Ω).Point ≃+ (E'⁄Ω).Point :=
    (Affine.Point.equivOfEq hC.symm).trans
      (Affine.Point.equivVariableChange (E'.baseChange Ω) C)
  refine ⟨e, ?_⟩
  have hu : σ (C.u : Ω) = C.u := congrArg (fun D : VariableChange Ω ↦ (D.u : Ω)) hσ
  have hr : σ C.r = C.r := congrArg VariableChange.r hσ
  have hs : σ C.s = C.s := congrArg VariableChange.s hσ
  have ht : σ C.t = C.t := congrArg VariableChange.t hσ
  rintro (_ | ⟨x,y,h⟩)
  · simp [e, ← Affine.Point.zero_def]
  · simp only [e, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some, Affine.Point.map_some]
    apply Affine.Point.some_eq_some <;> simp [hu, hr, hs, ht]

/-- Multiplicative reduction becomes split by an isomorphism intertwining inertia.
The unit discriminant argument also covers nonsplit reduction in residue characteristic two. -/
theorem exists_inertia_equivariant_split_twist {R K : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasMultiplicativeReduction R]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (A : ValuationSubring Ω)
    (hA : (A.comap (algebraMap K Ω)).toSubring = (algebraMap R K).range)
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K) :
    ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic) (_ : E'.HasSplitMultiplicativeReduction R)
      (e : (E⁄Ω).Point ≃+ (E'⁄Ω).Point),
      ∀ P, e (Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom P) =
        Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom (e P) := by
  obtain ⟨t,n,hD,hsplit⟩ := E.exists_split_twist_parameters (R := R)
  let E' := ((E.integralModel R).quadraticTwistOf t n).baseChange K
  have hE' : E' = E.quadraticTwistOf (algebraMap R K t) (algebraMap R K n) :=
    baseChange_integralModel_quadraticTwistOf E R t n
  have hDk : (algebraMap R K t) ^ 2 - 4 * algebraMap R K n ≠ 0 := by
    simpa only [map_sub, map_pow, map_mul, map_ofNat] using
      (hD.map (algebraMap R K)).ne_zero
  have hell : E'.IsElliptic := by
    rw [hE']
    exact E.isElliptic_quadraticTwistOf _ _ hDk
  let f : R →+* A := ((algebraMap K Ω).comp (algebraMap R K)).codRestrict A (by
    intro r
    change algebraMap R K r ∈ (A.comap (algebraMap K Ω)).toSubring
    rw [hA]
    exact ⟨r,rfl⟩)
  obtain ⟨x,hx⟩ := A.exists_quadratic_root (f t) (f n)
  have ht (r : R) : σ • f r = f r := Subtype.ext ((σ : Ω ≃ₐ[K] Ω).commutes _)
  have hfix : (σ : Ω ≃ₐ[K] Ω) (x : Ω) = x :=
    congrArg Subtype.val (A.inertia_fixes_quadratic_root (f t) (f n) x
      (by simpa only [map_sub, map_pow, map_mul, map_ofNat] using hD.map f) hx σ hσ (ht t) (ht n))
  let tΩ := algebraMap K Ω (algebraMap R K t)
  let nΩ := algebraMap K Ω (algebraMap R K n)
  have hxΩ : (x : Ω) ^ 2 - tΩ * x + nΩ = 0 := by
    exact congrArg Subtype.val hx
  have hw : tΩ - 2 * (x : Ω) ≠ 0 := by
    have heq : (tΩ - 2 * (x : Ω)) ^ 2 = tΩ ^ 2 - 4 * nΩ := by
      linear_combination 4 * hxΩ
    have hDΩ : tΩ ^ 2 - 4 * nΩ ≠ 0 := by
      simpa [tΩ, nΩ, map_ofNat] using ((map_ne_zero (algebraMap K Ω)).mpr hDk)
    exact fun h ↦ hDΩ (by rw [← heq,h,zero_pow (by decide)])
  let C : VariableChange Ω := ⟨Units.mk0 (tΩ - 2 * x) hw, 0,
    -((x : Ω) * (E.baseChange Ω).a₁),
    -((tΩ - 2 * x) ^ 2 * x * (E.baseChange Ω).a₃)⟩
  have hC : C • E'.baseChange Ω = E.baseChange Ω := by
    rw [hE', baseChange, quadraticTwistOf_map]
    exact quadraticRoot_variableChange_smul _ _ _ _ hxΩ hw
  have hCfix : C.map (σ : Ω ≃ₐ[K] Ω).toAlgHom.toRingHom = C := by
    ext <;> simp [C, VariableChange.map, tΩ, hfix, AlgEquiv.commutes, baseChange, map_ofNat]
  obtain ⟨e,he⟩ := exists_equivariant_pointEquiv_of_variableChange E E' C hC
    (σ : Ω ≃ₐ[K] Ω) hCfix
  exact ⟨E',hell,hsplit,e,he⟩

open ValuativeRel

/-- Inertia acts square-unipotently on prime-to-residue-characteristic torsion
at multiplicative reduction, whether split or nonsplit. -/
theorem inertia_sub_sub_eq_zero_of_multiplicative {K Ω : Type*}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasMultiplicativeReduction 𝒪[K]]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [DecidableEq Ω]
    (A : ValuationSubring Ω)
    (hA : (A.comap (algebraMap K Ω)).toSubring = (algebraMap 𝒪[K] K).range)
    {n : ℕ} (hn : IsUnit (n : A))
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    (P : (E⁄Ω).Point) (hP : n • P = 0) :
    Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom
        (Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom P - P) -
      (Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom P - P) = 0 := by
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨E',hell,hsplit,e,he⟩ := E.exists_inertia_equivariant_split_twist A hA σ hσ
  let := hell
  let := hsplit
  apply e.injective
  simp only [map_sub, map_zero, he]
  simpa only [map_sub] using E'.inertia_sub_sub_eq_zero_of_split_multiplicative Ω A hn σ hσ (e P)
    (by rw [← map_nsmul, hP, map_zero])

end WeierstrassCurve
