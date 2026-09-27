/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.Flat
public import FLT.EllipticCurve.FlatTorsion
public import FLT.FreyCurve.Basic
public import FLT.FreyCurve.Serre.LocalInertia
public import FLT.FreyCurve.Serre.LocalTorsion
public import FLT.FreyCurve.Serre.TateFlat
public import FLT.FreyCurve.Serre.Unramified

/-!
# Flatness of geometric torsion at good and split multiplicative places

The geometric torsion comparison transports the finite-flat model over a local
field to the restriction of the global torsion representation. Passing to
coefficient quotients then gives `IsFlatAt`.

The good-reduction case uses the existing `torsion_flat_of_good_reduction`
admission. The split multiplicative case uses the explicit finite-flat Kummer model.
The nonsplit case is supplied by `FLT.FreyCurve.Serre.NonsplitFlat`.
-/

@[expose] public section

open NumberField ValuativeRel

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

universe u

namespace WeierstrassCurve

variable {K : Type u} [Field K] [NumberField K]
  [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (E : WeierstrassCurve K) [E.IsElliptic] (n : ℕ) (hn : 0 < n)

set_option backward.isDefEq.respectTransparency false in
/-- A finite-flat model for local geometric torsion gives a finite-flat prolongation
of the global torsion representation restricted to that place. -/
theorem hasFlatProlongationAt_torsion_of_isFiniteFlat
    [DecidableEq (v.adicCompletion K)] [DecidableEq (AlgebraicClosure (v.adicCompletion K))]
    (hflat : GaloisModule.IsFiniteFlat (v.adicCompletionIntegers K) (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K))
      ((E.map (algebraMap K (v.adicCompletion K))).galoisRep n hn).Space) :
    (E.galoisRep n hn).HasFlatProlongationAt v := by
  classical
  let : (E.baseChange (v.adicCompletion K)).IsElliptic :=
    inferInstanceAs (E.map (algebraMap K (v.adicCompletion K))).IsElliptic
  let e := LinearEquiv.ofBijective (E.geometricTorsionBaseChange (L := v.adicCompletion K) n)
    (E.geometricTorsionBaseChange_bijective hn)
  let f : ((E.baseChange (v.adicCompletion K)).galoisRep n hn).Space →+[
      Field.absoluteGaloisGroup (v.adicCompletion K)] ((E.galoisRep n hn).toLocal v).Space :=
    { e.symm.toAddMonoidHom with
      map_smul' := by
        intro σ x
        apply e.injective
        change e (e.symm (_)) = e (((E.galoisRep n hn).toLocal v σ) (e.symm x))
        rw [e.apply_symm_apply]
        change _ = E.geometricTorsionBaseChange (L := v.adicCompletion K) n
          (((E.galoisRep n hn).toLocal v σ) (e.symm x))
        rw [E.geometricTorsionBaseChange_equivariant n hn]
        exact congrArg (((E.baseChange (v.adicCompletion K)).galoisRep n hn) σ)
          (e.apply_symm_apply x).symm }
  exact GaloisModule.IsFiniteFlat.map _ _ _ _ hflat f e.symm.bijective

/-- Good reduction at a completion gives a finite-flat prolongation of the global
torsion representation restricted to that place. -/
theorem hasFlatProlongationAt_torsion_of_goodReduction
    [(E.baseChange (v.adicCompletion K)).HasGoodReduction (v.adicCompletionIntegers K)] :
    (E.galoisRep n hn).HasFlatProlongationAt v := by
  classical
  let : (E.map (algebraMap K (v.adicCompletion K))).HasGoodReduction
      (v.adicCompletionIntegers K) :=
    inferInstanceAs ((E.baseChange (v.adicCompletion K)).HasGoodReduction
      (v.adicCompletionIntegers K))
  exact E.hasFlatProlongationAt_torsion_of_isFiniteFlat v n hn
    ((E.map (algebraMap K (v.adicCompletion K))).isFiniteFlat_torsion_of_goodReduction
      (v.adicCompletionIntegers K) (v.adicCompletion K) n hn)

/-- At a place of good reduction, prime torsion satisfies the flatness condition
for every open ideal of its coefficient field. -/
theorem isFlatAt_torsion_of_goodReduction [Fact n.Prime]
    [(E.baseChange (v.adicCompletion K)).HasGoodReduction (v.adicCompletionIntegers K)] :
    (E.galoisRep n hn).IsFlatAt v :=
  (E.hasFlatProlongationAt_torsion_of_goodReduction v n hn).isFlatAt v _

end WeierstrassCurve

namespace FreyCurve

/-- The good-reduction case of flatness at the Frey exponent prime. -/
theorem torsion_isFlatAt_of_goodReduction (P : FreyPackage)
    [(P.freyCurve.baseChange
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)).HasGoodReduction
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ)] :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  exact P.freyCurve.isFlatAt_torsion_of_goodReduction
    P.pp.toHeightOneSpectrumRingOfIntegersRat P.p P.hppos

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- At the exponent prime, split multiplicative Frey torsion has the explicit Kummer model. -/
theorem torsion_isFiniteFlat_of_splitMultiplicative (P : FreyPackage)
    [hsplit : (P.freyCurve.baseChange
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)).HasSplitMultiplicativeReduction
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
  let A := v.adicCompletionIntegers ℚ
  let : ValuativeRel K := completionValuativeRel v
  let : IsNonarchimedeanLocalField K := completion_isNonarchimedeanLocalField v
  let : (P.freyCurve.baseChange K).IsElliptic :=
    inferInstanceAs (P.freyCurve.map (algebraMap ℚ K)).IsElliptic
  let : (P.freyCurve.baseChange K).HasSplitMultiplicativeReduction 𝒪[K] := by
    have transport (B C : Subring K) [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
        [IsFractionRing B K] [IsFractionRing C K] (h : B = C) :
        (P.freyCurve.baseChange K).HasSplitMultiplicativeReduction B →
          (P.freyCurve.baseChange K).HasSplitMultiplicativeReduction C := by
      subst C
      exact id
    let : IsDiscreteValuationRing A.toSubring :=
      inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers ℚ))
    let : IsFractionRing A.toSubring K :=
      inferInstanceAs (IsFractionRing (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))
    exact transport A.toSubring 𝒪[K] (completion_integerRing_eq v).symm hsplit
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
  exact (P.freyCurve.baseChange K).isFiniteFlat_torsion_of_split_valuation
    A (completion_integerRing_eq v).symm P.p P.hppos b (inv_valuation_j_eq_pow P h2)

/-- Split multiplicative reduction at the exponent prime satisfies the Frey flatness field. -/
theorem torsion_isFlatAt_of_splitMultiplicative (P : FreyPackage)
    [(P.freyCurve.baseChange
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)).HasSplitMultiplicativeReduction
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ)] :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  let : Fact P.p.Prime := ⟨P.pp⟩
  exact (P.freyCurve.hasFlatProlongationAt_torsion_of_isFiniteFlat
    P.pp.toHeightOneSpectrumRingOfIntegersRat P.p P.hppos
    (torsion_isFiniteFlat_of_splitMultiplicative P)).isFlatAt _ _

end FreyCurve
