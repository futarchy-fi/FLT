/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuadraticTwistPoints
public import FLT.FreyCurve.Serre.TateFlat
public import FLT.GroupScheme.KummerTwist
public import FLT.GroupScheme.QuadraticTwistComparison

/-!
# Galois comparison for twisted Tate torsion

The same quadratic coefficient embedding controls both the curve twist and the
finite-flat Kummer model.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

open scoped TensorProduct WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

universe v
variable {R K : Type v} [CommRing R] [Field K] [CharZero K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra R K] [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
  [E'.HasSplitMultiplicativeReduction 𝒪[K]]
  (n : ℕ) (hn : 0 < n) [NeZero n] (u d : Rˣ) (r : R) (hr : 2 * r = 1)
  (b : Kˣ) (hq : E'.qUnit = b ^ n * Units.map (algebraMap R K).toMonoidHom u)
  [Algebra (QuadraticAlgebra R (d : R) 0) (AlgebraicClosure K)]
  [IsScalarTower R (QuadraticAlgebra R (d : R) 0) (AlgebraicClosure K)]

local notation "Ω" => AlgebraicClosure K
local notation "s" => IsScalarTower.toAlgHom R (QuadraticAlgebra R (d : R) 0) Ω

omit [CharZero K] in
include b hq in
/-- Matching the two quadratic signs yields an equivariant bijection for every Galois element. -/
theorem twistModel_comparison_of_signed
    (e : (E⁄Ω).Point ≃+ (E'⁄Ω).Point)
    (hfixed : ∀ σ : Ω ≃ₐ[K] Ω, (σ.toAlgHom.restrictScalars R).comp s = s →
      ∀ P, e (Affine.Point.map σ.toAlgHom P) = Affine.Point.map σ.toAlgHom (e P))
    (hneg : ∀ σ : Ω ≃ₐ[K] Ω,
      (σ.toAlgHom.restrictScalars R).comp s =
        (s).comp (QuadraticTwist.conjugation (d : R)).toAlgHom →
      ∀ P, e (Affine.Point.map σ.toAlgHom P) = -Affine.Point.map σ.toAlgHom (e P)) :
    let := KummerAlgebra.twistHopfAlgebra R n u d r hr
    ∃ f : Additive (K ⊗[R] KummerAlgebra.twistModel R n u d →ₐ[K] Ω) →+[
        Ω ≃ₐ[K] Ω] (E.galoisRep n hn).Space, Function.Bijective f := by
  let := KummerAlgebra.twistHopfAlgebra R n u d r hr
  let bΩ := Units.map (algebraMap K Ω).toMonoidHom b
  have hqΩ : E'.qUnitSepClosure Ω = bΩ ^ n * Units.map (algebraMap R Ω).toMonoidHom u := by
    change Units.map (algebraMap K Ω).toMonoidHom E'.qUnit = _
    rw [hq, map_mul, map_pow]
    rfl
  let ek := E'.kummerModelPointsAddEquiv n hn u bΩ hqΩ
  let eg : (K ⊗[R] KummerAlgebra.Coordinate R n u →ₐ[K] Ω) ≃*
      (K ⊗[R] KummerAlgebra.twistModel R n u d →ₐ[K] Ω) :=
    QuadraticTwist.genericPointsMulEquiv d r hr
  let eT : AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ) ≃+
      AddSubgroup.torsionBy (E'⁄Ω).Point (n : ℤ) :=
    { toFun := fun P ↦ ⟨e P, by
        change (n : ℤ) • e P = 0
        rw [← map_zsmul, show (n : ℤ) • P.val = 0 from P.property, map_zero]⟩
      invFun := fun P ↦ ⟨e.symm P, by
        change (n : ℤ) • e.symm P = 0
        rw [← map_zsmul, show (n : ℤ) • P.val = 0 from P.property, map_zero]⟩
      left_inv := fun P ↦ Subtype.ext (e.symm_apply_apply P)
      right_inv := fun P ↦ Subtype.ext (e.apply_symm_apply P)
      map_add' := fun P Q ↦ Subtype.ext (e.map_add P Q) }
  let ef := (eg.symm.toAdditive.trans ek).trans eT.symm
  have hef (φ) : e (ef φ : (E⁄Ω).Point) = ek (Additive.ofMul (eg.symm φ.toMul)) :=
    e.apply_symm_apply _
  have hek (σ : Ω ≃ₐ[K] Ω) (φ) :
      (ek (σ • φ) : (E'⁄Ω).Point) = Affine.Point.map σ.toAlgHom (ek φ) := by
    apply E'.kummerModelPointsAddEquiv_galois n hn u bΩ hqΩ σ
    apply Units.ext
    exact σ.commutes (b : K)
  refine ⟨{ ef.toAddMonoidHom with map_smul' := ?_ }, ef.bijective⟩
  intro σ φ
  apply Subtype.ext
  apply e.injective
  change e (ef (σ • φ) : (E⁄Ω).Point) = e (Affine.Point.map σ.toAlgHom (ef φ))
  rw [hef]
  rcases QuadraticTwist.coefficientMap_postcomp_cases d s
      (σ.toAlgHom.restrictScalars R) with hs | hs
  · rw [hfixed σ hs, hef]
    change (ek (Additive.ofMul (eg.symm (σ.toAlgHom.comp φ.toMul))) : (E'⁄Ω).Point) = _
    have hg : eg.symm (σ.toAlgHom.comp φ.toMul) =
        σ.toAlgHom.comp (eg.symm φ.toMul) :=
      QuadraticTwist.genericPointsMulEquiv_symm_fixed d r hr σ.toAlgHom hs φ.toMul
    rw [hg]
    exact hek σ _
  · rw [hneg σ hs, hef]
    change (ek (Additive.ofMul (eg.symm (σ.toAlgHom.comp φ.toMul))) : (E'⁄Ω).Point) = _
    have hg : ek (Additive.ofMul (eg.symm (σ.toAlgHom.comp φ.toMul))) =
        -ek (Additive.ofMul (σ.toAlgHom.comp (eg.symm φ.toMul))) :=
      QuadraticTwist.genericPointsMulEquiv_symm_conjugated d r hr
        ek.toAddMonoidHom σ.toAlgHom hs φ.toMul
    rw [hg]
    exact congrArg Neg.neg (hek σ _)

end WeierstrassCurve

namespace WeierstrassCurve

universe v
variable {R K : Type v} [CommRing R] [Field K] [CharZero K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra R K] [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (t c : R) (d : Rˣ) (hd : (d : R) = t ^ 2 - 4 * c)
  (n : ℕ) (hn : 0 < n) [NeZero n] (u : Rˣ) (r : R) (hr : 2 * r = 1)

local notation "Ω" => AlgebraicClosure K
local notation "E'" => E.quadraticTwistOf (algebraMap R K t) (algebraMap R K c)

include hd in
/-- Evaluating both twists at the same discriminant root matches all Galois signs. -/
theorem twistModel_comparison_of_root
    [(E').IsElliptic] [(E').HasSplitMultiplicativeReduction 𝒪[K]]
    (b : Kˣ) (hq : (E').qUnit = b ^ n * Units.map (algebraMap R K).toMonoidHom u)
    (x : Ω)
    (hx : x ^ 2 - algebraMap K Ω (algebraMap R K t) * x +
      algebraMap K Ω (algebraMap R K c) = 0)
    (hw : algebraMap K Ω (algebraMap R K t) - 2 * x ≠ 0) :
    let := KummerAlgebra.twistHopfAlgebra R n u d r hr
    ∃ f : Additive (K ⊗[R] KummerAlgebra.twistModel R n u d →ₐ[K] Ω) →+[
        Ω ≃ₐ[K] Ω] (E.galoisRep n hn).Space, Function.Bijective f := by
  let : Algebra R Ω := inferInstance
  let : IsScalarTower R K Ω := inferInstance
  let w := algebraMap K Ω (algebraMap R K t) - 2 * x
  have hw2 : w ^ 2 = algebraMap R Ω (d : R) := by
    rw [hd, map_sub, map_pow, map_mul, map_ofNat]
    simp only [IsScalarTower.algebraMap_apply R K Ω] at *
    dsimp [w]
    linear_combination 4 * hx
  let s : QuadraticAlgebra R (d : R) 0 →ₐ[R] Ω :=
    QuadraticAlgebra.lift ⟨w, by simpa [pow_two, Algebra.smul_def] using hw2⟩
  let : Algebra (QuadraticAlgebra R (d : R) 0) Ω := s.toRingHom.toAlgebra
  let : IsScalarTower R (QuadraticAlgebra R (d : R) 0) Ω := IsScalarTower.of_algHom s
  have hs : IsScalarTower.toAlgHom R (QuadraticAlgebra R (d : R) 0) Ω = s := rfl
  have hsw : s QuadraticAlgebra.omega = w := by simp [s, QuadraticAlgebra.lift]
  apply E.twistModel_comparison_of_signed E' n hn u d r hr b hq
    (E.quadraticRootPointEquiv (algebraMap R K t) (algebraMap R K c) x hx hw)
  · intro σ hσ P
    apply E.quadraticRootPointEquiv_discriminant_fixed _ _ x hx hw (by norm_num) σ _ P
    have h := AlgHom.congr_fun hσ QuadraticAlgebra.omega
    simp only [hs, AlgHom.comp_apply, hsw] at h
    exact h
  · intro σ hσ P
    apply E.quadraticRootPointEquiv_discriminant_negated _ _ x hx hw (by norm_num) σ _ P
    have h := AlgHom.congr_fun hσ QuadraticAlgebra.omega
    simp only [hs, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      QuadraticTwist.conjugation_omega, map_neg, hsw] at h
    exact h

end WeierstrassCurve
