/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.RootsOfUnityInertia
public import FLT.KnownIn1980s.EllipticCurves.TateCurve

/-!
# Inertia on split multiplicative torsion

Tate uniformization describes the deviation of a Galois automorphism on torsion
as a root of unity. The uniformization and its equivariance are existing admitted
inputs in `TateCurve`; the deductions here introduce no additional admissions.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]
  (Ω : Type*) [Field Ω] [Algebra k Ω]
  [DecidableEq Ω]

/-- Every torsion point has a Tate representative whose power is an integral power
of the Tate parameter. -/
theorem exists_tatePoint_of_nsmul_eq_zero {n : ℕ} (P : (E⁄Ω).Point)
    (hP : n • P = 0) :
    ∃ (u : Ωˣ) (m : ℤ), E.tatePoint Ω u = P ∧ u ^ n = E.qUnitSepClosure Ω ^ m := by
  obtain ⟨x, rfl⟩ := (E.tateEquivSepClosure Ω).surjective P
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : Additive.ofMul (u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = x :=
    congrArg Additive.ofMul hu
  rw [← hx] at hP ⊢
  have hpow : (↑(u ^ n) : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = 1 := by
    apply (E.tateEquivSepClosure Ω).injective
    rw [QuotientGroup.mk_pow]
    change E.tateEquivSepClosure Ω
      (n • Additive.ofMul (u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) =
        E.tateEquivSepClosure Ω 0
    simpa only [map_nsmul, map_zero] using hP
  obtain ⟨m, hm⟩ := (QuotientGroup.eq_one_iff _).mp hpow
  exact ⟨u, m, rfl, hm.symm⟩

variable [IsSepClosed Ω] [Algebra.IsSeparable k Ω]

/-- The deviation of a Galois automorphism on an `n`-torsion point is represented
by an `n`-th root of unity under Tate uniformization. -/
theorem exists_rootOfUnity_tatePoint_sub {n : ℕ} (σ : Ω ≃ₐ[k] Ω)
    (P : (E⁄Ω).Point) (hP : n • P = 0) :
    ∃ ζ : Ωˣ, ζ ^ n = 1 ∧
      E.tatePoint Ω ζ = Affine.Point.map σ.toAlgHom P - P := by
  obtain ⟨u, m, rfl, hu⟩ := E.exists_tatePoint_of_nsmul_eq_zero Ω P hP
  let τ : Ωˣ →* Ωˣ := Units.map σ.toAlgHom.toRingHom.toMonoidHom
  have hq : τ (E.qUnitSepClosure Ω) = E.qUnitSepClosure Ω := by
    apply Units.ext
    exact σ.commutes _
  refine ⟨τ u / u, ?_, ?_⟩
  · rw [div_pow, ← map_pow, hu, map_zpow, hq, div_self']
  · rw [E.tatePoint_galois]
    change E.tateEquivSepClosure Ω (Additive.ofMul ↑(τ u / u)) =
      E.tateEquivSepClosure Ω (Additive.ofMul ↑(τ u)) -
        E.tateEquivSepClosure Ω (Additive.ofMul ↑u)
    rw [← map_sub]
    apply congrArg
    exact QuotientGroup.mk_div _ (τ u) u

/-- Inertia acts square-unipotently on prime-to-residue-characteristic torsion of
a curve with split multiplicative reduction, by Tate uniformization. -/
theorem inertia_sub_sub_eq_zero_of_split_multiplicative
    (A : ValuationSubring Ω) {n : ℕ} (hn : IsUnit (n : A))
    (σ : A.decompositionSubgroup k) (hσ : σ ∈ A.inertiaSubgroup k)
    (P : (E⁄Ω).Point) (hP : n • P = 0) :
    Affine.Point.map (σ : Ω ≃ₐ[k] Ω).toAlgHom
        (Affine.Point.map (σ : Ω ≃ₐ[k] Ω).toAlgHom P - P) -
      (Affine.Point.map (σ : Ω ≃ₐ[k] Ω).toAlgHom P - P) = 0 := by
  obtain ⟨ζ, hζ, hPζ⟩ := E.exists_rootOfUnity_tatePoint_sub Ω (σ : Ω ≃ₐ[k] Ω) P hP
  have hfix : Units.map (σ : Ω ≃ₐ[k] Ω).toAlgHom.toRingHom.toMonoidHom ζ = ζ := by
    apply Units.ext
    exact A.inertia_fixes_of_pow_eq_one hn σ hσ (congrArg Units.val hζ)
  rw [← hPζ, E.tatePoint_galois, hfix, sub_self]

end WeierstrassCurve
