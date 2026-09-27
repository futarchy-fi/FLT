/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.Flat
public import FLT.FreyCurve.Serre.MultiplicativeFlat
public import FLT.FreyCurve.Serre.Semistable

/-!
# Flatness of Frey torsion at the exponent prime

The quadratic Kummer comparison supplies the nonsplit multiplicative case.
Together with good and split multiplicative reduction it gives the flatness field.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

open NumberField ValuativeRel
open scoped TensorProduct

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
-- Prefer the coordinate-algebra structures to the concrete valued-field candidates.
attribute [local instance 3000] QuadraticAlgebra.instAlgebra Subalgebra.algebra
  Algebra.TensorProduct.leftAlgebra

namespace FreyCurve

open scoped Classical in
/-- At a multiplicative exponent prime, the quadratic Kummer model realizes Frey torsion. -/
theorem torsion_twistModel_comparison (P : FreyPackage) :
    let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
    let K := v.adicCompletion ℚ
    let R := v.adicCompletionIntegers ℚ
    let Ω := AlgebraicClosure K
    letI : NeZero P.p := ⟨P.hppos.ne'⟩
    (P.freyCurve.baseChange K).HasMultiplicativeReduction R →
    ∃ (u d : Rˣ) (r : R) (hr : 2 * r = 1),
      letI : HopfAlgebra R (KummerAlgebra.twistModel R P.p u d) :=
        KummerAlgebra.twistHopfAlgebra R P.p u d r hr
      letI : Monoid (K ⊗[R] KummerAlgebra.twistModel R P.p u d →ₐ[K] Ω) :=
        instMonoidAlgHom_fLT K Ω (A := K ⊗[R] KummerAlgebra.twistModel R P.p u d)
      letI : MulDistribMulAction (Ω ≃ₐ[K] Ω)
          (K ⊗[R] KummerAlgebra.twistModel R P.p u d →ₐ[K] Ω) :=
        instMulDistribMulActionAlgEquivAlgHom_fLT K Ω
          (A := K ⊗[R] KummerAlgebra.twistModel R P.p u d)
      ∃ f : Additive (K ⊗[R] KummerAlgebra.twistModel R P.p u d →ₐ[K] Ω) →+[
        Ω ≃ₐ[K] Ω] ((P.freyCurve.map (algebraMap ℚ K)).galoisRep P.p P.hppos).Space,
        Function.Bijective f := by
  classical
  dsimp only
  intro hm
  let := hm
  let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let A := v.adicCompletionIntegers ℚ
  let : NeZero P.p := ⟨P.hppos.ne'⟩
  let : ValuativeRel K := completionValuativeRel v
  let : IsNonarchimedeanLocalField K := completion_isNonarchimedeanLocalField v
  let : (P.freyCurve.baseChange K).IsElliptic :=
    inferInstanceAs (P.freyCurve.map (algebraMap ℚ K)).IsElliptic
  let : (P.freyCurve.baseChange K).HasMultiplicativeReduction 𝒪[K] := by
    have transport (B C : Subring K) [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
        [IsFractionRing B K] [IsFractionRing C K] (h : B = C) :
        (P.freyCurve.baseChange K).HasMultiplicativeReduction B →
          (P.freyCurve.baseChange K).HasMultiplicativeReduction C := by
      subst C
      exact id
    let : IsDiscreteValuationRing A.toSubring :=
      inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers ℚ))
    let : IsFractionRing A.toSubring K :=
      inferInstanceAs (IsFractionRing (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))
    exact transport A.toSubring 𝒪[K] (completion_integerRing_eq v).symm hm
  have he : A.valuation.IsEquiv (ValuativeRel.valuation K) := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [A.valuation_le_one_iff]
    change x ∈ A.toSubring ↔ x ∈ (𝒪[K] : Subring K)
    rw [completion_integerRing_eq v]
  have h2A : IsUnit (2 : A) := prime_isUnit_adicCompletionIntegers Nat.prime_two P.pp (by
    have hp := P.hp5
    omega)
  have h2 : ValuativeRel.valuation K (2 : K) = 1 := by
    apply he.eq_one_iff_eq_one.mp
    have h := (A.valuation_eq_one_iff (2 : A)).mp h2A
    change A.valuation (A.subtype (2 : A)) = 1 at h
    simpa only [map_ofNat] using h
  have habc : ((P.a : ℚ) * P.b * P.c) ^ 2 ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0)
  let b : Kˣ := Units.mk0 (algebraMap ℚ K (((P.a : ℚ) * P.b * P.c) ^ 2))
    ((map_ne_zero (algebraMap ℚ K)).mpr habc)
  exact WeierstrassCurve.exists_twistModel_comparison_of_multiplicative_valuation
    A (completion_integerRing_eq v).symm h2A (P.freyCurve.baseChange K)
    P.p P.hppos b (inv_valuation_j_eq_pow P h2)

open scoped Classical in
/-- Multiplicative Frey torsion has a finite-flat quadratic Kummer model. -/
theorem torsion_isFiniteFlat_of_multiplicative (P : FreyPackage)
    [hm : (P.freyCurve.baseChange
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)).HasMultiplicativeReduction
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ)] :
    GaloisModule.IsFiniteFlat
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ)
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)
      (AlgebraicClosure (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
      ((P.freyCurve.map (algebraMap ℚ
        (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))).galoisRep
          P.p P.hppos).Space := by
  classical
  let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let : NeZero P.p := ⟨P.hppos.ne'⟩
  obtain ⟨u, d, r, hr, f, hf⟩ := torsion_twistModel_comparison P hm
  let := KummerAlgebra.twistHopfAlgebra R P.p u d r hr
  exact ⟨KummerAlgebra.twistModel R P.p u d, inferInstance, inferInstance,
    KummerAlgebra.twistModel_isFiniteFlat R P.p u d,
    KummerAlgebra.twistModel_generic_etale R P.p u d r hr K
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr P.hppos.ne')), f, hf⟩

/-- Good and both multiplicative cases give flatness at the Frey exponent prime. -/
theorem torsion_isFlatAt (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  let : Fact P.p.Prime := ⟨P.pp⟩
  let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
  obtain hg | hm := P.good_or_multiplicative (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
  · let := hg
    exact torsion_isFlatAt_of_goodReduction P
  · let := hm
    by_cases hs : (P.freyCurve.baseChange (v.adicCompletion ℚ)).HasSplitMultiplicativeReduction
        (v.adicCompletionIntegers ℚ)
    · let := hs
      exact torsion_isFlatAt_of_splitMultiplicative P
    · exact (P.freyCurve.hasFlatProlongationAt_torsion_of_isFiniteFlat v P.p P.hppos
        (torsion_isFiniteFlat_of_multiplicative P)).isFlatAt v _

end FreyCurve
