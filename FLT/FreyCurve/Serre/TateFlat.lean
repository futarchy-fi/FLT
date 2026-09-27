/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Torsion
public import FLT.FreyCurve.Serre.TateKummer
public import FLT.GroupScheme.KummerParameter
public import FLT.GroupScheme.KummerPoints

/-!
# Finite-flat models of split Tate torsion

A Tate parameter that is an `n`-th power times a unit has the Kummer Hopf
algebra as a finite-flat model of its torsion Galois module.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

universe v
variable {R K Ω : Type v} [CommRing R] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (E : WeierstrassCurve K) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[K]]
  [Field Ω] [Algebra K Ω] [DecidableEq Ω] [Algebra.IsAlgebraic K Ω]
  [Algebra R K] [Algebra R Ω] [IsScalarTower R K Ω]
  (n : ℕ) (hn : 0 < n) (u : Rˣ) (b : Ωˣ)
  (hq : E.qUnitSepClosure Ω = b ^ n * Units.map (algebraMap R Ω).toMonoidHom u)

omit [Algebra R K] [IsScalarTower R K Ω] in
/-- The integral Kummer points give Tate torsion, with convolution becoming addition. -/
theorem kummer_integral_convolution
    (f g : KummerAlgebra.Coordinate R n u →ₐ[R] Ω) :
    E.kummerTorsionPoint b (Units.map (algebraMap R Ω).toMonoidHom u) hq
      (KummerAlgebra.coordinateUnitPointsEquiv R n u hn (KummerAlgebra.convolution R n u hn f g)) =
    E.kummerTorsionPoint b (Units.map (algebraMap R Ω).toMonoidHom u) hq
      (KummerAlgebra.coordinateUnitPointsEquiv R n u hn f) +
    E.kummerTorsionPoint b (Units.map (algebraMap R Ω).toMonoidHom u) hq
      (KummerAlgebra.coordinateUnitPointsEquiv R n u hn g) := by
  obtain ⟨a, rfl⟩ := (KummerAlgebra.coordinateUnitPointsEquiv R n u hn).symm.surjective f
  obtain ⟨c, rfl⟩ := (KummerAlgebra.coordinateUnitPointsEquiv R n u hn).symm.surjective g
  rw [KummerAlgebra.coordinateUnitPointsEquiv_convolution]
  simp only [Equiv.apply_symm_apply]
  apply E.kummerTorsionPoint_add b (Units.map (algebraMap R Ω).toMonoidHom u) hq
    a c (KummerAlgebra.mulUnitPoint R n u hn a c) ((a.val.1.val + c.val.1.val) / n)
  · exact (Nat.mod_add_div _ _).symm
  · simp [KummerAlgebra.mulUnitPoint, div_eq_mul_inv]

/-- Integral Kummer coordinates commute with the Galois action when the scale is fixed. -/
theorem kummer_integral_galois (σ : Ω ≃ₐ[K] Ω)
    (hb : Units.map σ.toAlgHom.toRingHom.toMonoidHom b = b)
    (f : KummerAlgebra.Coordinate R n u →ₐ[R] Ω) :
    (E.kummerTorsionPoint b (Units.map (algebraMap R Ω).toMonoidHom u) hq
      (KummerAlgebra.coordinateUnitPointsEquiv R n u hn
        ((σ.toAlgHom.restrictScalars R).comp f)) : (E⁄Ω).Point) =
    Affine.Point.map σ.toAlgHom
      (E.kummerTorsionPoint b (Units.map (algebraMap R Ω).toMonoidHom u) hq
        (KummerAlgebra.coordinateUnitPointsEquiv R n u hn f)) := by
  obtain ⟨a, rfl⟩ := (KummerAlgebra.coordinateUnitPointsEquiv R n u hn).symm.surjective f
  rw [KummerAlgebra.coordinateUnitPointsEquiv_comp]
  simp only [Equiv.apply_symm_apply]
  exact E.kummerTorsionPoint_galois b (Units.map (algebraMap R Ω).toMonoidHom u) hq
    σ hb a (KummerAlgebra.mapUnitPoint R n u (σ.toAlgHom.restrictScalars R) a) rfl rfl

variable [NeZero n]

/-- The geometric Kummer-model bijection is additive for Hopf convolution. -/
noncomputable def kummerModelPointsAddEquiv :
    Additive (K ⊗[R] KummerAlgebra.Coordinate R n u →ₐ[K] Ω) ≃+
      AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ) where
  toEquiv := (Equiv.refl _).trans (E.kummerModelPointsEquiv n hn u b hq)
  map_add' f g := by
    change E.kummerTorsionPoint b (Units.map (algebraMap R Ω).toMonoidHom u) hq
        (KummerAlgebra.coordinateUnitPointsEquiv R n u hn
          (Bialgebra.restrictPoints R K Ω (KummerAlgebra.Coordinate R n u) (f.toMul * g.toMul))) = _
    rw [Bialgebra.restrictPoints_mul]
    exact E.kummer_integral_convolution n hn u b hq _ _

/-- The additive Kummer-model comparison is Galois-equivariant when the scale is fixed. -/
theorem kummerModelPointsAddEquiv_galois (σ : Ω ≃ₐ[K] Ω)
    (hb : Units.map σ.toAlgHom.toRingHom.toMonoidHom b = b)
    (f : Additive (K ⊗[R] KummerAlgebra.Coordinate R n u →ₐ[K] Ω)) :
    (E.kummerModelPointsAddEquiv n hn u b hq (σ • f) : (E⁄Ω).Point) =
      Affine.Point.map σ.toAlgHom (E.kummerModelPointsAddEquiv n hn u b hq f) := by
  exact E.kummer_integral_galois n hn u b hq σ hb
    (Bialgebra.restrictPoints R K Ω (KummerAlgebra.Coordinate R n u) f.toMul)

end WeierstrassCurve

namespace WeierstrassCurve

universe v
variable {R K : Type v} [CommRing R] [Field K] [CharZero K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra R K] [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (E : WeierstrassCurve K) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[K]]

/-- Split Tate torsion is finite flat when its parameter is an `n`-th power times a unit. -/
theorem isFiniteFlat_torsion_of_split_parameter
    (n : ℕ) (hn : 0 < n) (u : Rˣ) (b : Kˣ)
    (hq : E.qUnit = b ^ n * Units.map (algebraMap R K).toMonoidHom u) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) (E.galoisRep n hn).Space := by
  let Ω := AlgebraicClosure K
  let : NeZero n := ⟨hn.ne'⟩
  let bΩ := Units.map (algebraMap K Ω).toMonoidHom b
  have hqΩ : E.qUnitSepClosure Ω = bΩ ^ n * Units.map (algebraMap R Ω).toMonoidHom u := by
    change Units.map (algebraMap K Ω).toMonoidHom E.qUnit = _
    rw [hq, map_mul, map_pow]
    rfl
  let e := E.kummerModelPointsAddEquiv n hn u bΩ hqΩ
  let f : Additive (K ⊗[R] KummerAlgebra.Coordinate R n u →ₐ[K] Ω) →+[
      Field.absoluteGaloisGroup K] (E.galoisRep n hn).Space :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro σ φ
        apply Subtype.ext
        apply E.kummerModelPointsAddEquiv_galois n hn u bΩ hqΩ σ
        apply Units.ext
        exact σ.commutes (b : K) }
  exact ⟨KummerAlgebra.Coordinate R n u, inferInstance, inferInstance,
    KummerAlgebra.coordinate_isFiniteFlat R n u hn,
    KummerAlgebra.generic_etale R n u hn
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')), f, e.bijective⟩

end WeierstrassCurve

namespace WeierstrassCurve

universe v
variable {K : Type v} [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (E : WeierstrassCurve K) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[K]]

/-- Divisibility of the Tate parameter valuation gives a finite-flat model of split torsion. -/
theorem isFiniteFlat_torsion_of_split_valuation
    (A : ValuationSubring K) (hA : A.toSubring = (𝒪[K] : Subring K))
    (n : ℕ) (hn : 0 < n) (b : Kˣ)
    (hb : (valuation K E.j)⁻¹ = valuation K (b : K) ^ n) :
    GaloisModule.IsFiniteFlat A K (AlgebraicClosure K) (E.galoisRep n hn).Space := by
  have he : A.valuation.IsEquiv (valuation K) := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [A.valuation_le_one_iff]
    change x ∈ A.toSubring ↔ x ∈ (𝒪[K] : Subring K)
    rw [hA]
  have hq : valuation K (E.qUnit : K) = valuation K ((b : K) ^ n) := by
    change valuation K (tateParameter E.j) = _
    rw [valuation_tateParameter_eq E.one_lt_valuation_j, map_pow, hb]
  have hval := he.eq_iff.mpr hq
  rw [map_pow] at hval
  obtain ⟨u, hu⟩ := A.exists_unit_factor_of_valuation_eq_pow n E.qUnit b hval
  exact E.isFiniteFlat_torsion_of_split_parameter n hn u b hu

end WeierstrassCurve
